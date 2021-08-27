use crate::ir::*;
use specs::prelude::*;

impl Module {
    pub fn optimize(&mut self) {
        let mut dispatcher = DispatcherBuilder::new()
            .with(crate::simplify::Simplify, "simplify", &[])
            .build();
        dispatcher.setup(&mut self.world);
        dispatcher.dispatch(&mut self.world);
        dispatcher.dispose(&mut self.world);
    }
}
