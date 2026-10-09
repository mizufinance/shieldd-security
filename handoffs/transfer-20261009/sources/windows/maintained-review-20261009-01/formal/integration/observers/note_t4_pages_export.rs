// NEW combined stage, existing spool runner. One lowerer, 55 hash+1 tree page.
fn capture_note_t4_pages(prefix: &str) -> anyhow::Result<()> {
    use shieldd_sdk_circuits::hash::note_inspection::Role;
    let mut count = 0;
    let (compiled, copy) = catalogue::inspect_transfer_note_t4_pages(|ordinal, page| {
        anyhow::ensure!(
            ordinal == count && count < 56,
            "combined page callback order/overflow"
        );
        let body = match page {
            catalogue::NoteT4Page::Hash(page) => {
                let (role, level) = match page.hash.role {
                    Role::Commitment => ("commitment", 0),
                    Role::Nullifier => ("nullifier", 0),
                    Role::Dummy => ("dummy", 0),
                    Role::StateLevel(level) => ("state", level),
                };
                json!({"schema":"shieldd-transfer-note-hash-block-v1","family":"transfer",
                    "scope":"one input-note permutation cone and two note source LCs; tree wiring and native joins open",
                    "slot":page.hash.slot,"role":role,"level":level,"block":page.hash.block,
                    "hash":{"domain":page.hash.domain,"inputs":page.hash.inputs.iter().map(observed).collect::<Vec<_>>(),
                        "output":observed(&page.hash.output),"blocks":page.hash.blocks.iter().map(|b|json!({
                            "before":b.before.iter().map(observed).collect::<Vec<_>>(),"after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
                    "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                        "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
                    "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()})
            }
            catalogue::NoteT4Page::Tree(page) => {
                let note_handles = page.spends.selected();
                let note_expressions=page.selected.iter().zip(&page.expressions).filter(|(source,_)|note_handles.contains(source))
                    .map(|(source,terms)|json!({"source":index(source),"terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>();
                let spends=page.spends.spends.iter().map(|spend| {
                    let shared=&spend.shared;
                    let optional=spend.optional.as_ref().map(|o|json!({"domain":o.domain,"slot":o.slot,"seed":observed(&o.seed),
                        "synthetic":observed(&o.synthetic),"selected":observed(&o.selected),"products":o.products.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>()}));
                    json!({"shared":{"asset":observed(&shared.asset),"address":shared.address.iter().map(observed).collect::<Vec<_>>(),
                        "nk":observed(&shared.nk),"randomizer":observed(&shared.randomizer),"anchor":observed(&shared.anchor)},
                        "note":spend.note.iter().map(observed).collect::<Vec<_>>(),"commitment":observed(&spend.commitment),"position":observed(&spend.position),
                        "amount_bits":spend.amount_bits.iter().map(index).collect::<Vec<_>>(),"position_bits":spend.position_bits.iter().map(index).collect::<Vec<_>>(),
                        "real_nullifier":observed(&spend.real_nullifier),"computed_anchor":observed(&spend.computed_anchor),"nullifier":observed(&spend.nullifier),
                        "dummy":observed(&spend.dummy),"optional":optional})
                }).collect::<Vec<_>>();
                json!({"schema":"shieldd-transfer-note-tree-v1","family":"transfer",
                    "scope":"48 current note-only state levels and six source products each; actual rows/native joins open",
                    "domain":1,"depth":24,"levels":page.levels.iter().zip(page.products).map(|(level,products)|json!({
                        "slot":level.slot,"level":level.level,"node":observed(&level.node),"low":observed(&level.low),"high":observed(&level.high),
                        "siblings":level.siblings.iter().map(observed).collect::<Vec<_>>(),"swaps":level.swaps.iter().map(observed).collect::<Vec<_>>(),
                        "children":level.children.iter().map(observed).collect::<Vec<_>>(),"output":observed(&level.output),
                        "products":products.iter().map(|p|p.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>() })).collect::<Vec<_>>(),
                    "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                        "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
                    "spend":{"schema":"shieldd-transfer-note-spend-v1","family":"transfer",
                        "scope":"two current Transfer spend source roles and branch LCs; hash/tree/range/native joins open","spends":spends,
                        "expressions":note_expressions,"nodes":page.spend_nodes.iter().map(|(node,multiply,left,right)|json!({
                            "index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()}})
            }
        };
        anyhow::ensure!(
            serde_json::to_vec(&body)?.len() <= 4 * 1024 * 1024,
            "combined note page JSON exceeds4MiB"
        );
        write_packet_json(prefix, &format!("page{ordinal}.observations.json"), &body)?;
        count += 1;
        Ok(())
    })?;
    anyhow::ensure!(
        count == 56 && copy == 200692,
        "incomplete combined note pages/copy"
    );
    let spool = RowSpool::new(&compiled)?;
    ensure_original_shape(&spool.shape())?;
    spool.persist(prefix, "observer")?;
    drop(compiled);
    let identity = json!({"relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false});
    let mut pages = Vec::new();
    for ordinal in 0..56 {
        let mut body = read_packet_json(prefix, &format!("page{ordinal}.observations.json"))?;
        for (key, value) in identity.as_object().unwrap() {
            body.as_object_mut()
                .unwrap()
                .insert(key.clone(), value.clone());
        }
        if ordinal == 55 {
            for (key, value) in identity.as_object().unwrap() {
                body["spend"]
                    .as_object_mut()
                    .unwrap()
                    .insert(key.clone(), value.clone());
            }
        }
        write_packet_json(prefix, &format!("page{ordinal}.pending.json"), &body)?;
        let bytes = read_note_hash_page(prefix, ordinal)?;
        pages.push(if ordinal<55 {json!({"ordinal":ordinal,"slot":body["slot"],"role":body["role"],"level":body["level"],"block":body["block"],
            "blake3":packet_blake3(&bytes)})}else{json!({"ordinal":55,"slot":0,"role":"tree","level":0,"block":0,
            "blake3":packet_blake3(&bytes)})});
    }
    let mut manifest = identity;
    let object = manifest.as_object_mut().unwrap();
    object.insert("schema".into(), json!("shieldd-transfer-note-t4-pages-v1"));
    object.insert("family".into(), json!("transfer"));
    object.insert("scope".into(),json!("55 hash pages plus one two-spend/48-tree LC page from one lowering; native/kernel joins open"));
    object.insert("pages".into(), json!(pages));
    write_packet_json(prefix, "pending.json", &manifest)
}
fn qualify_note_t4_pages(first: &str, repeated: &str, pending: &Value) -> anyhow::Result<()> {
    let pages = pending["pages"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing56 note pages"))?;
    anyhow::ensure!(pages.len() == 56, "combined note page count");
    let mut hash_manifest = pending.clone();
    hash_manifest["pages"] = json!(&pages[..55]);
    qualify_note_hash_pages(first, repeated, &hash_manifest)?;
    let descriptor = &pages[55];
    anyhow::ensure!(
        descriptor.as_object().map(|d| d.len()) == Some(6)
            && descriptor["ordinal"] == 55
            && descriptor["slot"] == 0
            && descriptor["role"] == "tree"
            && descriptor["level"] == 0
            && descriptor["block"] == 0,
        "combined tree page descriptor"
    );
    let bytes = read_note_hash_page(first, 55)?;
    let repeat = read_note_hash_page(repeated, 55)?;
    anyhow::ensure!(
        bytes == repeat && descriptor["blake3"] == packet_blake3(&bytes),
        "combined tree page repeat/digest mismatch"
    );
    let page: Value = serde_json::from_slice(&bytes)?;
    anyhow::ensure!(
        page["schema"] == "shieldd-transfer-note-tree-v1"
            && page["domain"] == 1
            && page["depth"] == 24
            && page["levels"].as_array().map(|v| v.len()) == Some(48)
            && page["spend"]["schema"] == "shieldd-transfer-note-spend-v1",
        "combined tree/spend page shape mismatch"
    );
    for part in [&page, &page["spend"]] {
        anyhow::ensure!(
            part["ordinary_full_ordered_rows_equal"] == false
                && part["repeated_observations_equal"] == false,
            "combined page pending flags"
        );
        for key in [
            "relation_digest",
            "domain_size",
            "full_rows",
            "constant_copy",
        ] {
            anyhow::ensure!(part[key] == pending[key], "combined page identity mismatch");
        }
    }
    Ok(())
}
