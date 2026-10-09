// Included INSIDE catalogue.rs only in a fresh diagnostic source stage.
#[cfg(feature = "formal-observer")]
pub struct NoteSpendInspection {
    pub compiled: Compiled,
    pub report: crate::note::spend_inspection::Report,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_note_spend() -> Result<NoteSpendInspection> {
    use circuit::CircuitIdx;
    let _capture = crate::note::spend_inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let report = crate::note::spend_inspection::take()?;
    let selected = report.selected();
    let mut nodes = Vec::new();
    for product in &report.spends[1].optional.as_ref().unwrap().products {
        let [crate::scalar::inspection::Observed::Source(left), crate::scalar::inspection::Observed::Source(right), crate::scalar::inspection::Observed::Source(CircuitIdx::Node(output))] =
            product
        else {
            anyhow::bail!("optional branch product must have circuit source operands/result");
        };
        let (multiply, actual_left, actual_right) = c
            .inspect_node(*output)
            .ok_or_else(|| anyhow::anyhow!("missing optional branch product source"))?;
        anyhow::ensure!(
            multiply && *left == actual_left && *right == actual_right,
            "optional branch product source operand mismatch"
        );
        nodes.push((*output, multiply, actual_left, actual_right));
    }
    nodes.sort_by_key(|node| node.0);
    anyhow::ensure!(
        nodes.windows(2).all(|pair| pair[0].0 != pair[1].0),
        "aliased branch product sources"
    );
    let (relation, expressions, constant_copy) =
        Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(NoteSpendInspection {
        compiled: Compiled {
            family: Family::Transfer,
            relation,
            layout,
        },
        report,
        selected,
        expressions,
        constant_copy,
        nodes,
    })
}
