// New mode in the existing ownership exporter; never a second binary/runner.
fn capture_transfer_remaining_pages(scope:&str,prefix:&str)->anyhow::Result<()> {
    let mut descriptors=Vec::new();
    let (compiled,copy)=catalogue::inspect_transfer_remaining_pages(scope,|ordinal,page| {
        let hash=page.hash.map(|index| {let hash=&page.report.hashes[index];json!({
            "index":index,"scope":hash.scope,"domain":hash.domain,"inputs":hash.inputs.iter().map(observed).collect::<Vec<_>>(),
            "output":observed(&hash.output),"block":page.block,"blocks":hash.blocks.iter().map(|block|json!({
                "before":block.before.iter().map(observed).collect::<Vec<_>>(),
                "after":block.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()})});
        let body=json!({"schema":"shieldd-transfer-remaining-source-page-v1","family":"transfer",
            "scope":page.scope,"ordinal":ordinal,"qualification":false,
            "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,
            "records":page.report.records.iter().map(|record|json!({"scope":record.scope,"tag":record.tag,"ordinal":record.ordinal,
                "values":record.values.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "calls":page.report.hashes.iter().map(|hash|json!({"scope":hash.scope,"domain":hash.domain,
                "inputs":hash.inputs.iter().map(observed).collect::<Vec<_>>(),"output":observed(&hash.output),
                "blocks":hash.blocks.iter().map(|block|json!({"before":block.before.iter().map(observed).collect::<Vec<_>>(),
                    "after":block.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "hash":hash,"nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({
                "index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>(),
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({
                "source":index(source),"terms":terms.iter().map(|(column,coefficient)|
                    json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>()});
        let mut bytes=serde_json::to_vec(&body)?;bytes.push(b'\n');
        anyhow::ensure!(bytes.len()<=4*1024*1024,"remaining page JSON exceeds4MiB");
        let suffix=format!("pending-page-{ordinal:03}.json");
        write_packet_json(prefix,&suffix,&body)?;
        descriptors.push(json!({"ordinal":ordinal,"suffix":suffix,"bytes":bytes.len(),
            "blake3":packet_blake3(&bytes),"hash":page.hash,"block":page.block}));Ok(())
    })?;
    let spool=RowSpool::new(&compiled)?;ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(copy==200692,"remaining source constant copy changed");
    spool.persist(prefix,"observer")?;drop(compiled);
    write_packet_json(prefix,"pending.json",&json!({"schema":"shieldd-transfer-remaining-source-pages-v1",
        "family":"transfer","scope":scope,"pages":descriptors,"constant_copy":copy,
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"qualification":false,
        "semantic_status":"typed source/LC observations only; ordinary/repeat/kernel/native joins open"}))
}
