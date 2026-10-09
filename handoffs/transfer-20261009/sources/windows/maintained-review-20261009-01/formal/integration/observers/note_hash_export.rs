// Include in the existing ownership spool runner in a NEW stage only.
fn capture_note_hash(
    prefix: &str,
    slot: usize,
    role: &str,
    level: usize,
    block: usize,
) -> anyhow::Result<()> {
    use shieldd_sdk_circuits::hash::note_inspection::Role;
    let target = match (role, level) {
        ("commitment", 0) => Role::Commitment,
        ("nullifier", 0) => Role::Nullifier,
        ("dummy", 0) => Role::Dummy,
        ("state", level) if level < 24 => Role::StateLevel(level),
        _ => anyhow::bail!("invalid note hash role/level"),
    };
    let catalogue::NoteHashInspection {
        compiled,
        spends: _,
        hash,
        selected,
        expressions,
        constant_copy,
        nodes,
    } = catalogue::inspect_transfer_note_hash(slot, target, block)?;
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy == 200692, "note hash constant copy changed");
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let metadata = json!({"schema":"shieldd-transfer-note-hash-block-v1","family":"transfer",
        "scope":"one input-note permutation cone and two note source LCs; tree wiring and native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,
        "constant_copy":constant_copy,"ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,
        "slot":slot,"role":role,"level":level,"block":block,
        "hash":{"domain":hash.domain,"inputs":hash.inputs.iter().map(observed).collect::<Vec<_>>(),
            "output":observed(&hash.output),"blocks":hash.blocks.iter().map(|b|json!({
                "before":b.before.iter().map(observed).collect::<Vec<_>>(),
                "after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
            "left":index(left),"right":index(right)})).collect::<Vec<_>>()});
    write_packet_json(prefix, "pending.json", &metadata)
}
