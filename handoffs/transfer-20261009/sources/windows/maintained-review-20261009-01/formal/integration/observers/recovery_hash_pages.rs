// Future exporter include; full ordinary identity and false flags are attached
// by the same page sink. All recovery role LCs are retained in each hash page.
fn recovery_hash_page_json(page:&catalogue::RecoveryHashPage<'_>) -> Value {
    use shieldd_sdk_circuits::recovery::hash_inspection::Role;
    let role=match page.hash.role {Role::Secret=>"secret",Role::Confirmation=>"confirmation",
        Role::AmountStream=>"amount-stream",Role::BlindingStream=>"blinding-stream"};
    json!({"schema":"shieldd-transfer-recovery-hash-block-v1","family":"transfer",
        "scope":"one recovery secret11/2 confirmation21/4 or stream10/2 permutation with exact two capsule source roles; native/kernel joins open",
        "slot":page.hash.slot,"role":role,"level":0,"block":0,
        "hash":{"domain":page.hash.domain,"inputs":page.hash.inputs.iter().map(observed).collect::<Vec<_>>(),
            "output":observed(&page.hash.output),"blocks":[{
                "before":page.hash.before.iter().map(observed).collect::<Vec<_>>(),
                "after":page.hash.after.iter().map(observed).collect::<Vec<_>>()}]},
        "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(c,v)|json!([c,hex::encode(v.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
            "left":index(left),"right":index(right)})).collect::<Vec<_>>()})
}
