// Fresh diagnostic stage only; selected expressions retain full row compilation.
#[cfg(feature = "formal-observer")]
pub struct AssetMapInspection {
    pub compiled: Compiled,
    pub report: crate::map::asset_inspection::Report,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_asset_map() -> Result<AssetMapInspection> {
    let _capture = crate::map::asset_inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let report = crate::map::asset_inspection::take()?;
    use crate::scalar::inspection::Observed;
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    // Stop at the exact asset/hash ingress: their preceding hash DAG is a
    // separate certificate, not silently included in this bounded map cone.
    let roots: BTreeSet<_> = [&report.asset, &report.hash].into_iter()
        .filter_map(|v| match v { Observed::Source(i) => Some(*i), _ => None }).collect();
    let mut selected: BTreeSet<_> = report.selected().into_iter().collect();
    let mut pending: Vec<_> = selected.iter().copied().collect();
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) || roots.contains(&index) { continue; }
        anyhow::ensure!(visited.len() <= 16384, "asset map source cone exceeds 16384");
        if let CircuitIdx::Node(node) = index {
            let (multiply, left, right) = c.inspect_node(node)
                .ok_or_else(|| anyhow::anyhow!("missing asset map source node"))?;
            nodes.push((node, multiply, left, right));
            // Additive and native-scaled nodes are reconstructed symbolically
            // by typed ingress. Keep physical product pivots/operands, roles,
            // constants and witnesses, rather than every wide partial sum LC.
            if multiply && !matches!(left,CircuitIdx::Constant(_)) && !matches!(right,CircuitIdx::Constant(_)) {
                selected.extend([index,left,right]);
            }
            for child in [left, right] {
                pending.push(child);
            }
        } else {
            selected.insert(index);
        }
    }
    nodes.sort_by_key(|n| n.0);
    anyhow::ensure!(nodes.windows(2).all(|p| p[0].0 != p[1].0), "aliased map source nodes");
    anyhow::ensure!(selected.len() <= 4096, "asset map selected cone exceeds bound");
    let selected: Vec<_> = selected.into_iter().collect();
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    anyhow::ensure!(expressions.iter().map(Vec::len).sum::<usize>() <= 65536,
        "asset map expression terms exceed bound");
    Ok(AssetMapInspection { compiled: Compiled {family: Family::Transfer, relation, layout},
        report, selected, expressions, constant_copy, nodes })
}
