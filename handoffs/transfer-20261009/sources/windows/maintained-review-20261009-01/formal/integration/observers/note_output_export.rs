// Standalone bounded fallback in a NEW exporter source stage; emits PENDING.
// Activation must reuse full ordinary2 + repeated observation qualification.
fn capture_note_outputs(prefix: &str) -> anyhow::Result<()> {
    let catalogue::NoteOutputInspection { compiled,report,selected,expressions,constant_copy } =
        catalogue::inspect_transfer_note_outputs()?;
    let spool=RowSpool::new(&compiled)?;ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy==200692,"output constant copy changed");
    spool.persist(prefix,"observer")?;drop(compiled);
    let outputs=report.outputs.iter().map(|output| json!({
        "receiver":output.receiver,"note":output.note.iter().map(observed).collect::<Vec<_>>(),
        "amount_bits":output.amount_bits.iter().map(index).collect::<Vec<_>>(),
        "receiver_inverse":output.receiver_inverse.as_ref().map(observed),
        "computed_commitment":observed(&output.computed_commitment),"commitment":observed(&output.commitment),
        "capsule":output.capsule.iter().map(observed).collect::<Vec<_>>(),
        "capsule_commitment":observed(&output.capsule_commitment),
        "payload_key":output.payload_key.iter().map(observed).collect::<Vec<_>>()
    })).collect::<Vec<_>>();
    let metadata=json!({"schema":"shieldd-transfer-note-output-v1","family":"transfer",
        "scope":"two ordered receiver/change source roles and actual bindings/inverse/ranges; hash/recovery/native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,
        "constant_copy":constant_copy,"ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,
        "outputs":outputs,"expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
            "source":index(source),"terms":terms.iter().map(|(column,coefficient)|
                json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>()});
    write_packet_json(prefix,"pending.json",&metadata)
}
