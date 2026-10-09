// Include in catalogue.rs after note_hash_catalogue.rs in a later NEW stage.
#[cfg(feature = "formal-observer")]
fn inspect_note_tree_products(
    c: &circuit::Circuit<Scalar>,
    level: &crate::tree::note_inspection::Level,
) -> Result<Vec<[crate::scalar::inspection::Observed; 3]>> {
    use crate::scalar::inspection::Observed;
    use circuit::CircuitIdx;
    let source = |v: &Observed| -> Result<CircuitIdx> {
        match v {
            Observed::Source(index) => Ok(*index),
            Observed::Native(_) => {
                anyhow::bail!("note tree wiring must have actual source handles")
            }
        }
    };
    let mut result = Vec::new();
    for (output, bit) in level.swaps.iter().map(|v| (v, &level.low)) {
        let CircuitIdx::Node(node) = source(output)? else {
            anyhow::bail!("note tree swap not a source node")
        };
        let (multiply, left, right) = c
            .inspect_node(node)
            .ok_or_else(|| anyhow::anyhow!("missing note tree swap"))?;
        anyhow::ensure!(
            multiply && left == source(bit)?,
            "note tree low swap operation changed"
        );
        result.push([
            Observed::Source(left),
            Observed::Source(right),
            output.clone(),
        ]);
    }
    for child in &level.children {
        let CircuitIdx::Node(node) = source(child)? else {
            anyhow::bail!("note tree child not a source node")
        };
        let (multiply, _false_side, product) = c
            .inspect_node(node)
            .ok_or_else(|| anyhow::anyhow!("missing note tree select"))?;
        let CircuitIdx::Node(product_node) = product else {
            anyhow::bail!("note tree select product missing")
        };
        anyhow::ensure!(!multiply, "note tree select is not false plus product");
        let (multiply, left, right) = c
            .inspect_node(product_node)
            .ok_or_else(|| anyhow::anyhow!("missing note tree high product"))?;
        anyhow::ensure!(
            multiply && left == source(&level.high)?,
            "note tree high select operation changed"
        );
        result.push([
            Observed::Source(left),
            Observed::Source(right),
            Observed::Source(product),
        ]);
    }
    anyhow::ensure!(result.len() == 6, "note tree six product inventory changed");
    Ok(result)
}
