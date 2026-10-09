// Fresh-stage helpers: stop at each actual permutation input, not at a digest.
#[cfg(feature = "formal-observer")]
pub struct OutputHashPage<'a> {
    pub hash: &'a crate::note::output_hash_inspection::Report,
    pub outputs: &'a crate::note::output_inspection::Report,
    pub selected: &'a [circuit::CircuitIdx], pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub struct AssetHashPage<'a> {
    pub hash: &'a crate::hash::asset_hash_inspection::Report,
    pub map_input: &'a crate::scalar::inspection::Observed,
    pub selected: &'a [circuit::CircuitIdx], pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
fn transfer_hash_page_cone(
    c: &circuit::Circuit<Scalar>, selected: Vec<circuit::CircuitIdx>,
    before: &[crate::scalar::inspection::Observed], after: &[crate::scalar::inspection::Observed],
    boundaries: &[&crate::scalar::inspection::Observed], width: usize,
) -> Result<(Vec<circuit::CircuitIdx>, Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>)> {
    use crate::scalar::inspection::Observed;
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    anyhow::ensure!(before.len() == width && after.len() == width && matches!(width, 3|6),
        "actual hash checkpoint width changed");
    let roots: BTreeSet<_> = before.iter().filter_map(|v| match v {
        Observed::Source(i) => Some(*i), _ => None }).collect();
    let mut selected: BTreeSet<_> = selected.into_iter().collect();
    for value in before.iter().chain(after).chain(boundaries.iter().copied()) {
        if let Observed::Source(index) = value { selected.insert(*index); }
    }
    let mut pending: Vec<_> = after.iter().filter_map(|v| match v {
        Observed::Source(i) => Some(*i), _ => None }).collect();
    let mut visited = BTreeSet::new(); let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) || roots.contains(&index) { continue; }
        anyhow::ensure!(visited.len() <= 16384, "actual permutation cone exceeds 16384");
        match index {
            CircuitIdx::Node(node) => {
                let (multiply,left,right) = c.inspect_node(node)
                    .ok_or_else(||anyhow::anyhow!("missing actual permutation node"))?;
                nodes.push((node,multiply,left,right));
                if multiply && !matches!(left,CircuitIdx::Constant(_)) && !matches!(right,CircuitIdx::Constant(_)) {
                    selected.extend([index,left,right]);
                }
                pending.extend([left,right]);
            }
            CircuitIdx::Constant(_) => { selected.insert(index); }
            CircuitIdx::Witness(_) => anyhow::bail!("undeclared actual permutation witness"),
        }
    }
    nodes.sort_by_key(|node|node.0);
    anyhow::ensure!(selected.len() <= 4096, "actual permutation selected handles exceed 4096");
    Ok((selected.into_iter().collect(),nodes))
}
#[cfg(feature = "formal-observer")]
fn output_hash_page_cone(c: &circuit::Circuit<Scalar>, outputs: &crate::note::output_inspection::Report,
    hash: &crate::note::output_hash_inspection::Report,
) -> Result<(Vec<circuit::CircuitIdx>, Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>)> {
    anyhow::ensure!(hash.block < 2 && hash.blocks.len() == 2, "output hash block changed");
    let block = &hash.blocks[hash.block];
    let boundaries: Vec<_> = hash.inputs.iter().chain(std::iter::once(&hash.output))
        .chain(hash.blocks.iter().flat_map(|b|b.before.iter().chain(&b.after))).collect();
    transfer_hash_page_cone(c,outputs.selected(),&block.before,&block.after,&boundaries,6)
}
#[cfg(feature = "formal-observer")]
fn asset_hash_page_cone(c: &circuit::Circuit<Scalar>, hash: &crate::hash::asset_hash_inspection::Report,
) -> Result<(Vec<circuit::CircuitIdx>, Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>)> {
    transfer_hash_page_cone(c,Vec::new(),&hash.before,&hash.after,&[&hash.asset,&hash.output],3)
}
