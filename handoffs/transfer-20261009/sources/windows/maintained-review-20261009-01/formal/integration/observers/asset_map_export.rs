// Existing owned spool runner in a fresh stage. Qualification stays pending.
fn capture_asset_map(prefix: &str) -> anyhow::Result<()> {
    let catalogue::AssetMapInspection { compiled, report, selected, expressions, constant_copy, nodes } =
        catalogue::inspect_transfer_asset_map()?;
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy == 200692, "asset-map constant copy changed");
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let metadata = json!({"schema":"shieldd-transfer-asset-map-v1", "family":"transfer",
        "scope":"one balance asset-map source boundary; actual rows/hash/native/codec joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,
        "constant_copy":constant_copy,"ordinary_full_ordered_rows_equal":false,
        "repeated_observations_equal":false,"asset":observed(&report.asset),"hash":observed(&report.hash),
        "values":report.values.iter().map(observed).collect::<Vec<_>>(),
        "y_bits":report.y_bits.iter().map(index).collect::<Vec<_>>(),
        "cofactor":report.cofactor.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "cofactor_aux":report.cofactor_aux.iter().map(|a|a.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "constraint_products":report.constraint_products.iter().map(observed).collect::<Vec<_>>(),
        "qr":report.qr.iter().map(observed).collect::<Vec<_>>(),
        "canonical":report.canonical.iter().map(observed).collect::<Vec<_>>(),
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())]))
                .collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
            "left":index(left),"right":index(right)})).collect::<Vec<_>>()});
    anyhow::ensure!(serde_json::to_vec(&metadata)?.len() <= 4 * 1024 * 1024, "asset-map metadata exceeds bound");
    write_packet_json(prefix, "pending.json", &metadata)
}
