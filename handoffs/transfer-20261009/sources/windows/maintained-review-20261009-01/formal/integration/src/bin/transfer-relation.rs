//! Stream the ordinary Transfer relation; no witness, setup or proving occurs.
use commonware_codec::Encode;
use commonware_cryptography::zk::circuit::CircuitIdx;
use serde_json::json;
use shieldd_sdk_circuits::{catalogue, proof::Family};
use std::io::{self, Write};

fn index(value: &CircuitIdx) -> serde_json::Value {
    match value {
        CircuitIdx::Constant(i) => json!([0, i]),
        CircuitIdx::Witness(i) => json!([1, i]),
        CircuitIdx::Node(i) => json!([2, i]),
    }
}

fn main() -> anyhow::Result<()> {
    let compiled = catalogue::compile(Family::Transfer)?;
    let relation = &compiled.relation;
    anyhow::ensure!(relation.public_inputs() == 1 && relation.blocks() == [1],
        "Transfer requires exactly one public input and one single-value committed block");
    anyhow::ensure!(compiled.layout.public().len() == 1 && compiled.layout.blocks().len() == 1
        && compiled.layout.blocks()[0].len() == 1, "Transfer layout shape changed");
    anyhow::ensure!(relation.inspect_committed_start() == 2, "Transfer committed offset changed");
    let rows = relation.inspect_rows();
    let mut output = io::BufWriter::new(io::stdout().lock());
    serde_json::to_writer(&mut output, &json!({
        "schema": "shieldd-transfer-relation-v1", "family": "transfer",
        "relation_digest": hex::encode(relation.digest()),
        "domain_size": relation.domain_size(), "stored_rows": rows.len(),
        "public_inputs": relation.public_inputs(), "committed_blocks": relation.blocks(),
        "constant_column": 0, "public_columns": [1], "committed_columns": [[relation.inspect_committed_start()]],
        "source_public": compiled.layout.public().iter().map(index).collect::<Vec<_>>(),
        "source_blocks": compiled.layout.blocks().iter().map(|b| b.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "coefficient_encoding": "canonical-big-endian-32",
        "field_modulus": "52435875175126190479447740508185965837690552500527637822603658699938581184513",
        "role_provenance": "constant0/public prefix and committed_start=1+public_count in exact compiler",
        "padding": "implicit-all-zero-rows-to-domain-size"
    }))?;
    writeln!(output)?;
    for (i, (a, b)) in rows.enumerate() {
        let terms = |xs: &[(u32, commonware_cryptography::bls12381::primitives::group::Scalar)]| {
            xs.iter().map(|(column, coefficient)| json!([column, hex::encode(coefficient.encode())])).collect::<Vec<_>>()
        };
        serde_json::to_writer(&mut output, &json!({"row": i, "a": terms(a), "b": terms(b)}))?;
        writeln!(output)?;
    }
    serde_json::to_writer(&mut output, &json!({"eof": true, "rows": relation.inspect_rows().len()}))?;
    writeln!(output)?;
    output.flush()?;
    Ok(())
}
