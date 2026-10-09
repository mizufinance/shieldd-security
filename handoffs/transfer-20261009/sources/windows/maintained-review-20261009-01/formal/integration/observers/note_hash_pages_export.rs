// Existing spool runner only, NEW stage. Ordinary2+repeat qualification remains
// in qualified_metadata; this adds exact bounded page-byte checks to that path.
fn capture_note_hash_pages(prefix: &str) -> anyhow::Result<()> {
    use shieldd_sdk_circuits::hash::note_inspection::Role;
    let mut count = 0;
    let (compiled, constant_copy) = catalogue::inspect_transfer_note_hash_pages(
        |ordinal, page| {
            anyhow::ensure!(
                ordinal == count && count < 55,
                "note hash page callback order/overflow"
            );
            let (role, level) = match page.hash.role {
                Role::Commitment => ("commitment", 0),
                Role::Nullifier => ("nullifier", 0),
                Role::Dummy => ("dummy", 0),
                Role::StateLevel(level) => ("state", level),
            };
            let body = json!({"slot":page.hash.slot,"role":role,"level":level,"block":page.hash.block,
            "hash":{"domain":page.hash.domain,"inputs":page.hash.inputs.iter().map(observed).collect::<Vec<_>>(),
                "output":observed(&page.hash.output),"blocks":page.hash.blocks.iter().map(|b|json!({
                    "before":b.before.iter().map(observed).collect::<Vec<_>>(),
                    "after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
                "left":index(left),"right":index(right)})).collect::<Vec<_>>()});
            anyhow::ensure!(
                serde_json::to_vec(&body)?.len() <= 4 * 1024 * 1024,
                "note hash page JSON exceeds4MiB"
            );
            write_packet_json(prefix, &format!("page{ordinal}.observations.json"), &body)?;
            // The owned page cone/LCs and JSON are dropped before the next callback.
            count += 1;
            Ok(())
        },
    )?;
    anyhow::ensure!(
        count == 55 && constant_copy == 200692,
        "incomplete note hash page run/copy"
    );
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let mut pages = Vec::new();
    for ordinal in 0..55 {
        let mut body = read_packet_json(prefix, &format!("page{ordinal}.observations.json"))?;
        let object = body
            .as_object_mut()
            .ok_or_else(|| anyhow::anyhow!("note hash page not object"))?;
        for (key,value) in [
            ("schema",json!("shieldd-transfer-note-hash-block-v1")),("family",json!("transfer")),
            ("scope",json!("one input-note permutation cone and two note source LCs; tree wiring and native joins open")),
            ("relation_digest",json!(hex::encode(spool.digest))),("domain_size",json!(spool.domain)),
            ("full_rows",json!(spool.rows)),("constant_copy",json!(constant_copy)),
            ("ordinary_full_ordered_rows_equal",json!(false)),("repeated_observations_equal",json!(false))] {
            object.insert(key.into(),value);
        }
        write_packet_json(prefix, &format!("page{ordinal}.pending.json"), &body)?;
        let bytes = read_note_hash_page(prefix, ordinal)?;
        pages.push(
            json!({"ordinal":ordinal,"slot":body["slot"],"role":body["role"],"level":body["level"],
            "block":body["block"],"blake3":packet_blake3(&bytes)}),
        );
    }
    // Only successful completion creates this manifest. Partial callback files
    // cannot enter the ordinary/repeat qualifier without it.
    write_packet_json(
        prefix,
        "pending.json",
        &json!({"schema":"shieldd-transfer-note-hash-pages-v1","family":"transfer",
        "scope":"55 bounded input-note permutation pages from one lowering; tree wiring/native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":constant_copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"pages":pages}),
    )
}
fn read_note_hash_page(prefix: &str, ordinal: usize) -> anyhow::Result<Vec<u8>> {
    let file = File::open(format!("{prefix}.page{ordinal}.pending.json"))?;
    let mut bytes = Vec::new();
    file.take(4 * 1024 * 1024 + 1).read_to_end(&mut bytes)?;
    anyhow::ensure!(
        !bytes.is_empty() && bytes.len() <= 4 * 1024 * 1024,
        "note hash page byte bound"
    );
    Ok(bytes)
}
fn qualify_note_hash_pages(first: &str, repeated: &str, pending: &Value) -> anyhow::Result<()> {
    let pages = pending["pages"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing note hash page inventory"))?;
    anyhow::ensure!(pages.len() == 55, "note hash manifest page count");
    for (ordinal, descriptor) in pages.iter().enumerate() {
        let slot = if ordinal >= 27 { 1usize } else { 0usize };
        let offset = if slot == 0 { ordinal } else { ordinal - 27 };
        let (role, level, block) = match offset {
            0..=1 => ("commitment", 0, offset),
            2 => ("nullifier", 0, 0),
            3..=26 => ("state", offset - 3, 0),
            27 if slot == 1 => ("dummy", 0, 0),
            _ => anyhow::bail!("invalid native note hash page inventory"),
        };
        anyhow::ensure!(
            descriptor.as_object().map(|d| d.len()) == Some(6)
                && descriptor["slot"] == slot
                && descriptor["role"] == role
                && descriptor["level"] == level
                && descriptor["block"] == block,
            "note hash native role inventory mismatch"
        );
        anyhow::ensure!(
            descriptor["ordinal"] == ordinal,
            "note hash page inventory ordering"
        );
        let bytes = read_note_hash_page(first, ordinal)?;
        let repeat = read_note_hash_page(repeated, ordinal)?;
        anyhow::ensure!(bytes == repeat, "repeated note hash page bytes mismatch");
        anyhow::ensure!(
            descriptor["blake3"] == packet_blake3(&bytes),
            "note hash page digest mismatch"
        );
        let page: Value = serde_json::from_slice(&bytes)?;
        for key in ["slot", "role", "level", "block"] {
            anyhow::ensure!(
                descriptor[key] == page[key],
                "note hash page descriptor mismatch"
            );
        }
        anyhow::ensure!(
            page["schema"] == "shieldd-transfer-note-hash-block-v1"
                && page["ordinary_full_ordered_rows_equal"] == false
                && page["repeated_observations_equal"] == false,
            "note hash page pending schema/flags mismatch"
        );
        for key in [
            "relation_digest",
            "domain_size",
            "full_rows",
            "constant_copy",
        ] {
            anyhow::ensure!(
                page[key] == pending[key],
                "note hash page/manifest identity mismatch"
            );
        }
    }
    Ok(())
}
