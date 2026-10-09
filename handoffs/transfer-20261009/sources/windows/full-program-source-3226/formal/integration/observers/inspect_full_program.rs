/// Read the complete source program without evaluating or changing any value.
/// These accessors are diagnostic-only additions in a fresh source stage.
pub fn inspect_program_counts(&self) -> (u32, usize, usize, usize) {
    (self.witnesses, self.constants.len(), self.nodes.len(), self.assertions.len())
}

pub fn inspect_program_constant(&self, index: usize) -> Option<&F> {
    self.constants.get(index)
}

pub fn inspect_program_node(&self, index: usize) -> Option<(bool, CircuitIdx, CircuitIdx)> {
    self.nodes.get(index).map(|node| match *node {
        CircuitNode::Add(left, right) => (false, left, right),
        CircuitNode::Mul(left, right) => (true, left, right),
    })
}

pub fn inspect_program_assertion(&self, index: usize) -> Option<(CircuitIdx, CircuitIdx)> {
    self.assertions.get(index).copied()
}
