use crate::ir::*;
use specs::prelude::*;
use specs::Component;
use std::collections::HashMap;

pub struct SSA;

#[derive(Clone, PartialEq, Eq, Debug, Component)]
pub enum FunMode {
    /// Stores the continuation
    SSA(Val),
    CPS,
    /// Stores the parent
    Block(Val),
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

        let mut not_block = Vec::new();
        let (mut can_be_block, mut uses, mut ssa_reqs) = (&entities, &slots, &uses_comp)
            .join()
            .filter_map(|(v, slot, uses)| match slot {
                Slot::Full(Node::Fun(_)) => {
                    // It can only be a block if all uses are direct calls
                    let mut block = true;
                    let mut uses2 = Vec::new();
                    let mut ssa_reqs = Vec::new();
                    for &i in &**uses {
                        match slots.node(i).unwrap() {
                            Node::Fun(Function {
                                callee, call_args, ..
                            }) => match slots.node(*callee).unwrap() {
                                _ if *callee == v => uses2.push(i),
                                Node::If(_) | Node::IfCase(_, _) | Node::Ref(_, _) => uses2.push(i),
                                Node::ExternCall(_, _) if *call_args.last().unwrap() == v => {
                                    uses2.push(i)
                                }
                                Node::Fun(_) if *call_args.last().unwrap() == v => {
                                    uses2.push(i);
                                    ssa_reqs.push(slots.unredirect(*callee));
                                }
                                _ => {
                                    block = false;
                                    break;
                                }
                            },
                            Node::Param(_, _) => (),
                            _ => {
                                block = false;
                                break;
                            }
                        }
                    }
                    Some((
                        v,
                        block,
                        if block {
                            // If this requires something to be SSA, then that can't be a block
                            // Either way something isn't a block, and this is generally a better idea
                            not_block.extend(ssa_reqs.iter().copied());
                            uses2
                        } else {
                            Vec::new()
                        },
                        ssa_reqs,
                    ))
                }
                _ => None,
            })
            .fold(
                (HashMap::new(), HashMap::new(), HashMap::new()),
                |(mut ha, mut hb, mut hc), (k, a, b, c)| {
                    ha.insert(k, a);
                    hb.insert(k, b);
                    hc.insert(k, c);
                    (ha, hb, hc)
                },
            );
        for i in not_block {
            if can_be_block.get(&i).copied().unwrap_or(false) {
                can_be_block.insert(i, false);
                uses.insert(i, Vec::new());
            }
        }

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
                                // if j doesn't end up being a block, this can't either since j uses this
                                let mut ssa_reqs_j = ssa_reqs[&j].clone();
                                ssa_reqs.get_mut(&i).unwrap().append(&mut ssa_reqs_j);

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
                    cont.filter(|&cont| {
                        let cuses = uses_comp.get(cont).unwrap();
                        !cuses.is_empty() && cuses.iter().all(|&i| {
                            matches!(slots.node(i), Some(Node::Fun(Function { callee, call_args, .. }))
                                // Theoretically, we support multiple return values by packing them in a struct
                                // But LLVM doesn't support GC pointers in structs right now, so it's disabled
                                if *callee == cont && call_args.len() == 1)
                        })
                    })
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
                            _ if can_be_block[&r] => {
                                nreqs.extend(&ssa_reqs[&r]);
                            }
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

        for (&v, &is_block) in &can_be_block {
            let is_block = is_block
                && ssa_reqs[&v]
                    .iter()
                    .all(|f| reqs.contains_key(f) && !can_be_block[&f]);
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
        return blocks.contains_key(&callee)
            || call_args.is_empty()
            || try_stack_call(*call_args.last().unwrap(), cont, &[], reqs, blocks, slots);
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
