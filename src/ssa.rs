use std::collections::{HashMap, HashSet};

use crate::ir::*;
use specs::prelude::*;
use specs::Component;

pub struct SSA;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Component)]
pub enum FunMode {
    /// Stores the continuation
    SSA(Val),
    CPS,
    /// Stores the parent
    Block(Val),
}

/// Returns all functions that `v` depends on the parameters of, and so must be within, recursively.
pub fn dependencies(v: Val, slots: &ReadStorage<Slot>) -> Vec<Val> {
    fn go(slots: &ReadStorage<Slot>, v: Val, seen: &mut HashSet<Val>, acc: &mut HashSet<Val>) {
        let v = slots.unredirect(v);
        match slots.node(v).unwrap() {
            Node::Param(f, _) => {
                if seen.contains(f) {
                } else {
                    match slots.node(*f).unwrap() {
                        Node::Fun(Function { .. }) => {
                            acc.insert(*f);
                        }
                        // Parameters of pi or sigma types don't count
                        Node::FunType(_) | Node::ProdType(_) => (),
                        _ => unreachable!(),
                    }
                }
            }
            n @ Node::Fun(_) => {
                if !seen.contains(&v) {
                    seen.insert(v);
                    for i in n.runtime_args() {
                        go(slots, i, seen, acc)
                    }
                    seen.remove(&v);
                }
            }
            n => {
                for i in n.runtime_args() {
                    go(slots, i, seen, acc)
                }
            }
        }
    }
    let mut acc = HashSet::new();
    go(slots, v, &mut HashSet::new(), &mut acc);
    acc.into_iter().collect()
}

impl<'a> System<'a> for SSA {
    type SystemData = (
        Entities<'a>,
        ReadStorage<'a, Uses>,
        ReadStorage<'a, Slot>,
        WriteStorage<'a, FunMode>,
    );

    fn setup(&mut self, world: &mut World) {
        world.register::<FunMode>();
    }

    fn run(&mut self, (entities, uses_comp, slots, mut modes): Self::SystemData) {
        // Stage 1: figure out which functions are blocks of which others

        let (mut can_be_block, mut uses): (HashMap<Val, bool>, HashMap<Val, Vec<Val>>) =
            (&entities, &slots, &uses_comp)
                .join()
                .filter_map(|(v, slot, uses)| match slot {
                    Slot::Full(Node::Fun(_)) => {
                        // It can only be a block if all uses are direct calls
                        let mut block = true;
                        let mut uses2 = Vec::new();
                        for &i in &**uses {
                            match slots.node(i).unwrap() {
                                Node::Fun(Function { callee, .. }) if *callee == v => uses2.push(i),
                                Node::Param(_, _) => (),
                                _ => {
                                    block = false;
                                    break;
                                }
                            }
                        }
                        Some(((v, block), (v, if block { uses2 } else { Vec::new() })))
                    }
                    _ => None,
                })
                .unzip();
        // for v in entities.join() {
        //     if slots.fun(v).is_some() {
        //         for i in dependencies(v, &slots) {
        //             if can_be_block[&i] {
        //                 uses.entry(i).or_default().push(v);
        //             }
        //         }
        //     }
        // }

        let mut parents: HashMap<Val, Val> = HashMap::new();

        let mut i = 0;
        while uses.values().any(|x| !x.is_empty()) {
            i += 1;
            // println!(
            //     "Iteration {}:\nuses = {:?}\ncan_be_block = {:?}\nparent = {:?}\n",
            //     i, uses, can_be_block, parents
            // );
            if i > 1000 {
                panic!("Infinite loop in SSA::run()");
            }
            let keys = uses.keys().copied().collect::<Vec<_>>();
            for i in keys {
                if can_be_block[&i] {
                    for j in uses[&i].clone() {
                        if !can_be_block[&j] {
                            uses.get_mut(&i).unwrap().retain(|&x| x != j);
                            // j is a function, so that must be our parent function
                            if parents.get(&i).map_or(true, |x| *x == j) {
                                parents.insert(i, j);
                            } else {
                                // we already have a different parent, so i can't be a block
                                can_be_block.insert(i, false);
                                uses.insert(i, Vec::new());
                                break;
                            }
                        } else {
                            // j can be a block
                            if parents
                                .get(&j)
                                .map_or(false, |x| parents.get(&i).map_or(false, |y| x != y))
                            {
                                // incompatible parents
                                can_be_block.insert(i, false);
                                uses.insert(i, Vec::new());
                                break;
                            }

                            fn rec(x: Val, i: Val, v: &HashMap<Val, Vec<Val>>) -> bool {
                                x == i || { v[&x].len() == 1 && rec(v[&x][0], i, v) }
                            }

                            // if it has no uses, use its parent and remove it from uses
                            if uses[&j].iter().all(|&x| rec(x, i, &uses)) {
                                uses.get_mut(&i).unwrap().retain(|&x| x != j);
                                if let Some(&pj) = parents.get(&j).or(parents.get(&i)) {
                                    parents.insert(j, pj);
                                    if parents.get(&i).map_or(true, |x| *x == pj) {
                                        parents.insert(i, pj);
                                    } else {
                                        // we already have a different parent, so i can't be a block
                                        can_be_block.insert(i, false);
                                        uses.insert(i, Vec::new());
                                        break;
                                    }
                                } else {
                                    // Neither one has a parent
                                    parents.insert(i, j);
                                }
                            }
                        }
                    }
                }
            }
        }
        // If it doesn't have a parent, it's not a block
        for (v, is_block) in &mut can_be_block {
            if *is_block && !parents.contains_key(v) {
                *is_block = false;
            }
        }

        // Stage 2: figure out which top-level functions are SSA-compatible and which must stay CPS

        // Not in reqs = a block, or not SSA
        // Empty Vec in reqs = definitely SSA
        // Nonempty Vec in reqs = might be SSA
        let (conts, mut reqs): (HashMap<_, _>, HashMap<_, _>) = can_be_block
            .iter()
            .filter_map(|(&v, &is_block)| {
                if is_block {
                    None
                } else {
                    let fun = slots.node(v).unwrap();
                    let cont = match fun {
                        Node::Fun(Function { params, .. }) if !params.is_empty() => {
                            let l = params.len() as u8;
                            match slots.node(*params.last().unwrap()).unwrap() {
                                Node::FunType(_) => {
                                    let uses: Vec<Val> = uses_comp
                                        .get(v)
                                        .unwrap()
                                        .iter()
                                        .copied()
                                        .filter(|&u| match slots.node(u).unwrap() {
                                            Node::Param(_, i) => *i == l - 1,
                                            _ => false,
                                        })
                                        .collect();
                                    if uses.len() == 1 {
                                        Some(uses[0])
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    cont.filter(|&cont| !uses_comp.get(cont).unwrap().is_empty())
                        .and_then(|cont| {
                            let mut reqs = Vec::new();
                            if try_stack_call(v, cont, &[], &mut reqs, &can_be_block, &slots) {
                                Some(((v, cont), (v, reqs)))
                            } else {
                                None
                            }
                        })
                }
            })
            .unzip();
        let mut any_left = true;
        while any_left {
            any_left = false;
            let keys: Vec<_> = reqs.keys().copied().collect();
            for val in keys {
                let vreqs = &reqs[&val];
                if !vreqs.is_empty() {
                    // The new version of reqs - functions we're still waiting on
                    let mut nreqs = Vec::new();
                    let mut okay = true;

                    for &r in vreqs {
                        let r = slots.unredirect(r);
                        // Single recursion is fine
                        if r == val {
                            continue;
                        }
                        match reqs.get(&r) {
                            _ if can_be_block[&r] => (),
                            Some(v) if v.is_empty() => {
                                // We won't add it to nreqs, since we know it's good
                            }
                            None => {
                                okay = false;
                                break;
                            }
                            Some(v) => {
                                // Transfer that function's requirements to this one.
                                // We'll come back next iteration.
                                nreqs.extend(
                                    v.iter()
                                        .copied()
                                        .filter(|&x| {
                                            x != r
                                                && x != val
                                                && !nreqs.contains(&x)
                                                && !vreqs.contains(&x)
                                        })
                                        .collect::<Vec<_>>(),
                                );
                            }
                        }
                    }

                    if !okay {
                        reqs.remove(&val).unwrap();
                    } else if nreqs.is_empty() {
                        reqs.insert(val, nreqs);
                    } else {
                        reqs.insert(val, nreqs);
                        any_left = true;
                    }
                }
            }
        }

        // Stage 3: set the FunModes appropriately

        for (v, is_block) in can_be_block {
            let mode = if is_block {
                FunMode::Block(*parents.get(&v).unwrap())
            } else if reqs.contains_key(&v) {
                FunMode::SSA(conts[&v])
            } else {
                FunMode::CPS
            };
            modes.insert(v, mode).unwrap();
        }
    }
}

/// A helper for SSA construction: returns whether we can call `callee` on the stack, adding requirements to `reqs`.
fn try_stack_call(
    callee: Val,
    cont: Val,
    call_args: &[Val],
    reqs: &mut Vec<Val>,
    blocks: &HashMap<Val, bool>,
    slots: &ReadStorage<Slot>,
) -> bool {
    if reqs.contains(&callee) {
        return true;
    }
    match slots.node(callee).unwrap() {
        // If we call another function's parameter, we can't be stack enabled.
        // Even if this is another function's continuation, we have our own continuation.
        Node::Param(_, _) => callee == cont,
        // If it's calling ifcase or if, it could call any of the call arguments
        Node::IfCase(_, _) | Node::If(_) => {
            for i in call_args {
                if !try_stack_call(*i, cont, &[], reqs, blocks, slots) {
                    return false;
                }
            }
            true
        }
        // If it's calling an extern function, it calls the passed continuation
        Node::ExternCall(_, _) | Node::Ref(_, _) => {
            try_stack_call(*call_args.last().unwrap(), cont, &[], reqs, blocks, slots)
        }
        // Unreachable and Stop don't call any other functions
        Node::Const(_) => true,
        Node::Fun(f) => {
            reqs.push(callee);
            try_stack_call(f.callee, cont, &f.call_args, reqs, blocks, slots)
            // If it's stack enabled, it will call its continuation
            && (blocks.contains_key(&callee) || call_args.is_empty() || try_stack_call(*call_args.last().unwrap(), cont, &[], reqs, blocks, slots))
        }
        // It's an unknown function, which might not be stack-enabled
        _ => false,
    }
}
