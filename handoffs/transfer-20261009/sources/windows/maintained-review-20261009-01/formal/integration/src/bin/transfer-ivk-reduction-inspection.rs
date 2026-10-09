//! Bounded source/linear metadata and exact observer noninterference checks.
#[cfg(feature = "formal-observer")]
fn main() -> anyhow::Result<()> {
    use commonware_codec::Encode;
    use commonware_cryptography::zk::circuit::CircuitIdx;
    use serde_json::json;
    use shieldd_sdk_circuits::{catalogue, proof::Family};
    let index = |value: &CircuitIdx| match value {
        CircuitIdx::Constant(i) => json!([0, i]),
        CircuitIdx::Witness(i) => json!([1, i]),
        CircuitIdx::Node(i) => json!([2, i]),
    };
    let observe = |value: &shieldd_sdk_circuits::scalar::inspection::Observed| match value {
        shieldd_sdk_circuits::scalar::inspection::Observed::Source(source)=>json!({"source":index(source)}),
        shieldd_sdk_circuits::scalar::inspection::Observed::Native(value)=>json!({"native":hex::encode(value.encode())}),
    };
    let observed = catalogue::inspect_transfer_ivk_reduction()?;
    for _ in 0..2 {
        let ordinary = catalogue::compile(Family::Transfer)?;
        anyhow::ensure!(ordinary.layout == observed.compiled.layout
            && ordinary.relation.domain_size() == observed.compiled.relation.domain_size()
            && ordinary.relation.digest() == observed.compiled.relation.digest(), "ordinary shape/digest mismatch");
        let ordinary_rows = ordinary.relation.inspect_rows();
        let observed_rows = observed.compiled.relation.inspect_rows();
        anyhow::ensure!(ordinary_rows.len() == observed_rows.len()
            && ordinary_rows.zip(observed_rows).all(|(left, right)| left == right),
            "ordinary full ordered rows differ from inspected compilation");
    }
    let repeated = catalogue::inspect_transfer_ivk_reduction()?;
    anyhow::ensure!(repeated.ivk_hash_handles == observed.ivk_hash_handles && repeated.report == observed.report && repeated.selected == observed.selected && repeated.expressions == observed.expressions
        && repeated.constant_copy == observed.constant_copy && repeated.nodes == observed.nodes,
        "repeated inspection metadata changed");
    {
      let repeated_rows = repeated.compiled.relation.inspect_rows();
      let first_rows = observed.compiled.relation.inspect_rows();
      anyhow::ensure!(repeated.compiled.layout == observed.compiled.layout
        && repeated.compiled.relation.domain_size() == observed.compiled.relation.domain_size()
        && repeated.compiled.relation.digest() == observed.compiled.relation.digest()
        && repeated_rows.len() == first_rows.len()
        && repeated_rows.zip(first_rows).all(|(left, right)| left == right),
          "repeated full ordered relation changed");
    }
    drop(repeated);
    let metadata = json!({
        "schema": "shieldd-transfer-ivk-reduction-inspection-v1",
        "relation_digest": hex::encode(observed.compiled.relation.digest()),
        "domain_size": observed.compiled.relation.domain_size(),
        "stored_rows": observed.compiled.relation.inspect_rows().len(),
        "ordinary_full_ordered_rows_equal": true,
        "scope": "source handles and pre-outline linear combinations only; semantic row certificates remain open",
        "constant_copy": observed.constant_copy,
        "domain": 16,
        "arity": 3,
        "hash_handles": observed.ivk_hash_handles.iter().map(&index).collect::<Vec<_>>(),
        "value": index(&observed.report.value),
        "quotient": index(&observed.report.quotient),
        "remainder": index(&observed.report.remainder),
        "quotient_bits": observed.report.quotient_bits.iter().map(&index).collect::<Vec<_>>(),
        "remainder_bits": observed.report.remainder_bits.iter().map(&index).collect::<Vec<_>>(),
        "quotient_end": observe(&observed.report.quotient_end),
        "remainder_end": observe(&observed.report.remainder_end),
        "terminal_end": observe(&observed.report.terminal_end),
        "equation": index(&observed.report.equation),
        "terminal_gate": index(&observed.report.terminal_gate),
        "consumer": observed.report.consumer.map(|(value,inverse)|json!([index(&value),index(&inverse)])),
        "steps": observed.report.steps.iter().map(|steps|steps.iter().map(|values|values.iter().map(&observe).collect::<Vec<_>>()).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "expressions": observed.selected.iter().zip(&observed.expressions).map(|(source, terms)| json!({
            "source": index(source), "terms": terms.iter().map(|(column, coefficient)|
                json!([column, hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes": observed.nodes.iter().map(|(node, multiply, left, right)|
            json!({"index": node, "multiply": multiply, "left": index(left), "right": index(right)})).collect::<Vec<_>>()
    });
    println!("{}", serde_json::to_string(&metadata)?);
    Ok(())
}

#[cfg(not(feature = "formal-observer"))]
fn main() { panic!("requires formal-observer feature"); }
