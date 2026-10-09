// Future exporter fragment. Existing observed/index/Scalar codec are reused.
// Identity fields and false qualification flags are attached by the full-spool sink.
fn recovery_capsule_roles_json(reports:&[shieldd_sdk_circuits::recovery::capsule_inspection::Report;2],
    selected:&[CircuitIdx],expressions:&[Vec<(u32,commonware_cryptography::bls12381::primitives::group::Scalar)>]) -> Value {
    let mut handles=reports.iter().flat_map(|report|report.selected()).collect::<Vec<_>>();
    handles.sort();handles.dedup();
    json!({"schema":"shieldd-transfer-recovery-capsule-roles-v1","family":"transfer",
        "scope":"two output recovery source roles including both EPK inverses; scalar/group/hash/native joins open",
        "capsules":reports.iter().map(|report| {let core=&report.core;json!({
            "payload_key":core.payload_key.iter().map(observed).collect::<Vec<_>>(),
            "amount":observed(&core.amount),"blinding":observed(&core.blinding),
            "randomizer":observed(&core.randomizer),"bits":core.bits.iter().map(index).collect::<Vec<_>>(),
            "seed":observed(&core.seed),"capsule":core.capsule.iter().map(observed).collect::<Vec<_>>(),
            "commitment":observed(&core.commitment),"computed_epk":core.computed_epk.iter().map(observed).collect::<Vec<_>>(),
            "shared":core.shared.iter().map(observed).collect::<Vec<_>>(),"secret":observed(&core.secret),
            "computed_c2":observed(&core.computed_c2),"epk_inverse":observed(&core.epk_inverse),
            "computed_confirmation":observed(&report.computed_confirmation),
            "amount_stream":observed(&report.amount_stream),"computed_amount":observed(&report.computed_amount),
            "blinding_stream":observed(&report.blinding_stream),"computed_blinding":observed(&report.computed_blinding),
            "plaintext_inverse":observed(&report.plaintext_inverse)})}).collect::<Vec<_>>(),
        "expressions":selected.iter().zip(expressions).filter(|(source,_)|handles.contains(source))
            .map(|(source,terms)|json!({"source":index(source),"terms":terms.iter()
                .map(|(column,value)|json!([column,hex::encode(value.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>()})
}
