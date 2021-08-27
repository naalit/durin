use crate::ir::*;
use specs::prelude::*;
use std::collections::HashSet;

pub struct Simplify;

impl<'a> System<'a> for Simplify {
    type SystemData = (
        Entities<'a>,
        WriteStorage<'a, Uses>,
        ReadStorage<'a, Slot>,
        ReadStorage<'a, Name>,
    );

    fn run(&mut self, (entities, mut uses, slots, names): Self::SystemData) {
        // Remove unused values
        // This first calculates the set of all values reachable from named values (an approximation for public visibility)
        // and then removes everything else
        let mut used = HashSet::new();
        let mut stack = Vec::new();
        for (i, _) in (&entities, &names).join() {
            let i = slots.unredirect(i);
            stack.push(i);
            used.insert(i);
        }
        while let Some(i) = stack.pop() {
            for a in slots.node(i).into_iter().flat_map(Node::args) {
                let a = slots.unredirect(a);
                if !used.contains(&a) {
                    stack.push(a);
                    used.insert(a);
                }
            }
        }
        // let mut cnt = 0;
        for val in entities.join() {
            if !used.contains(&slots.unredirect(val)) {
                for i in slots.node(val).into_iter().flat_map(Node::args) {
                    let i = slots.unredirect(i);
                    if used.contains(&i) {
                        uses.get_mut(i).map(|x| x.retain(|y| *y != val));
                    }
                }
                // cnt += 1;
                entities.delete(val).unwrap();
            }
        }
        // eprintln!("Removed {} unused values", cnt);
    }

    fn dispose(self, world: &mut World) {
        world.maintain();
    }
}
