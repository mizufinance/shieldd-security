//! Bounded AK subgroup metadata, with full ordinary/observer relation parity.
use commonware_codec::Encode;
use commonware_cryptography::zk::circuit::CircuitIdx;
use serde_json::json;
use shieldd_sdk_circuits::{catalogue, proof::Family};

fn index(value: &CircuitIdx) -> serde_json::Value {
    match value {
        CircuitIdx::Constant(i) => json!([0, i]),
        CircuitIdx::Witness(i) => json!([1, i]),
        CircuitIdx::Node(i) => json!([2, i]),
    }
}
fn same(left: &catalogue::Compiled, right: &catalogue::Compiled) -> bool {
    left.layout == right.layout && left.relation.domain_size() == right.relation.domain_size()
        && left.relation.digest() == right.relation.digest()
        && left.relation.public_inputs() == right.relation.public_inputs()
        && left.relation.blocks() == right.relation.blocks()
        && left.relation.inspect_rows().len() == right.relation.inspect_rows().len()
        && left.relation.inspect_rows().zip(right.relation.inspect_rows()).all(|(a,b)| a == b)
}
fn main() -> anyhow::Result<()> {
    eprintln!("capture AK subgroup");
    let observed = catalogue::inspect_transfer_ak_subgroup()?;
    for _ in 0..2 {
        eprintln!("ordinary full ordered relation comparison");
        let ordinary = catalogue::compile(Family::Transfer)?;
        anyhow::ensure!(same(&ordinary, &observed.compiled), "ordinary AK observer relation mismatch");
    }
    eprintln!("repeat AK capture");
    let repeated = catalogue::inspect_transfer_ak_subgroup()?;
    anyhow::ensure!(same(&repeated.compiled, &observed.compiled)
        && repeated.report == observed.report && repeated.ivk_handles == observed.ivk_handles
        && repeated.selected == observed.selected && repeated.expressions == observed.expressions
        && repeated.constant_copy == observed.constant_copy && repeated.nodes == observed.nodes,
        "repeated AK capture mismatch");
    drop(repeated);
    let relation = &observed.compiled.relation;
    anyhow::ensure!(relation.public_inputs() == 1 && relation.blocks() == [1]
        && observed.compiled.layout.public().len() == 1 && observed.compiled.layout.blocks().len() == 1
        && observed.compiled.layout.blocks()[0].len() == 1, "Transfer shape changed");
    let report = &observed.report;
    println!("{}", serde_json::to_string(&json!({
        "schema": "shieldd-transfer-ak-subgroup-v1", "family": "transfer",
        "scope": "bounded AK cofactor/on-curve/nonidentity source observation; row and group joins open",
        "relation_digest": hex::encode(relation.digest()), "domain_size": relation.domain_size(),
        "full_rows": relation.inspect_rows().len(), "constant_copy": observed.constant_copy,
        "ivk_handles": observed.ivk_handles.iter().map(index).collect::<Vec<_>>(),
        "inputs": report.inputs.iter().map(index).collect::<Vec<_>>(),
        "curve": report.curve.iter().map(index).collect::<Vec<_>>(),
        "doubles": report.doubles.iter().map(|row| row.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "spans": report.spans,
        "nonidentity": report.nonidentity.iter().map(index).collect::<Vec<_>>(),
        "nonidentity_product": index(&report.nonidentity_product),
        "expressions": observed.selected.iter().zip(&observed.expressions).map(|(source, terms)| json!({
            "source": index(source), "terms": terms.iter().map(|(column, coefficient)|
                json!([column, hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes": observed.nodes.iter().map(|(node, multiply, left, right)| json!({
            "index": node, "multiply": multiply, "left": index(left), "right": index(right) })).collect::<Vec<_>>()
    }))?);
    Ok(())
}
