// Included in the EXISTING formal-owned spool exporter in a fresh source stage.
// New dispatch: ["note-spend-spool", prefix] => capture_note_spend(prefix).
// The existing ordinary spill / full ordered compare / repeat qualifier must
// run in separate processes before flags can become true. This emits PENDING.
fn capture_note_spend(prefix: &str) -> anyhow::Result<()> {
    let catalogue::NoteSpendInspection {
        compiled,
        report,
        selected,
        expressions,
        constant_copy,
        nodes,
    } = catalogue::inspect_transfer_note_spend()?;
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy == 200692, "note-spend constant copy changed");
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let spends = report.spends.iter().map(|spend| {
        let shared = &spend.shared;
        let optional = spend.optional.as_ref().map(|o| json!({
            "domain":o.domain, "slot":o.slot, "seed":observed(&o.seed),
            "synthetic":observed(&o.synthetic), "selected":observed(&o.selected),
            "products":o.products.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>()
        }));
        json!({"shared":{"asset":observed(&shared.asset),
            "address":shared.address.iter().map(observed).collect::<Vec<_>>(),
            "nk":observed(&shared.nk), "randomizer":observed(&shared.randomizer), "anchor":observed(&shared.anchor)},
            "note":spend.note.iter().map(observed).collect::<Vec<_>>(),
            "commitment":observed(&spend.commitment), "position":observed(&spend.position),
            "amount_bits":spend.amount_bits.iter().map(index).collect::<Vec<_>>(),
            "position_bits":spend.position_bits.iter().map(index).collect::<Vec<_>>(),
            "real_nullifier":observed(&spend.real_nullifier), "computed_anchor":observed(&spend.computed_anchor),
            "nullifier":observed(&spend.nullifier), "dummy":observed(&spend.dummy), "optional":optional})
    }).collect::<Vec<_>>();
    let metadata = json!({"schema":"shieldd-transfer-note-spend-v1", "family":"transfer",
        "scope":"two current Transfer spend source roles and branch LCs; hash/tree/range/native joins open",
        "relation_digest":hex::encode(spool.digest), "domain_size":spool.domain,
        "full_rows":spool.rows, "constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":false, "repeated_observations_equal":false,
        "spends":spends,
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source), "terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({
            "index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
    write_packet_json(prefix, "pending.json", &metadata)
}
