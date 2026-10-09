fn output_roles_json(report:&shieldd_sdk_circuits::note::output_inspection::Report,
    selected:&[CircuitIdx],expressions:&[Vec<(u32,commonware_cryptography::bls12381::primitives::group::Scalar)>]) -> Value {
    let handles=report.selected();
    json!({"schema":"shieldd-transfer-note-output-v1","family":"transfer",
        "scope":"two ordered receiver/change source roles and actual bindings/inverse/ranges; hash/recovery/native joins open",
        "outputs":report.outputs.iter().map(|output|json!({"receiver":output.receiver,
            "note":output.note.iter().map(observed).collect::<Vec<_>>(),"amount_bits":output.amount_bits.iter().map(index).collect::<Vec<_>>(),
            "receiver_inverse":output.receiver_inverse.as_ref().map(observed),"computed_commitment":observed(&output.computed_commitment),
            "commitment":observed(&output.commitment),"capsule":output.capsule.iter().map(observed).collect::<Vec<_>>(),
            "capsule_commitment":observed(&output.capsule_commitment),"payload_key":output.payload_key.iter().map(observed).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),"expressions":selected.iter().zip(expressions).filter(|(source,_)|handles.contains(source))
            .map(|(source,terms)|json!({"source":index(source),"terms":terms.iter().map(|(c,v)|json!([c,hex::encode(v.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>()})
}
fn output_hash_page_json(page:&catalogue::OutputHashPage<'_>) -> Value {
    use shieldd_sdk_circuits::note::output_hash_inspection::Role;
    let (role,supplied)=match page.hash.role {
        Role::Note=>("note",&page.outputs.outputs[page.hash.slot].commitment),
        Role::Recovery=>("recovery",&page.outputs.outputs[page.hash.slot].capsule_commitment),
    };
    json!({"schema":"shieldd-transfer-note-output-hash-block-v1","family":"transfer",
        "scope":"one output NOTE15/8 or recovery20/7 permutation and exact two-output source roles; native/kernel joins open",
        "slot":page.hash.slot,"role":role,"level":0,"block":page.hash.block,
        "supplied_commitment":observed(supplied),"hash":{"domain":page.hash.domain,
            "inputs":page.hash.inputs.iter().map(observed).collect::<Vec<_>>(),"output":observed(&page.hash.output),
            "blocks":page.hash.blocks.iter().map(|b|json!({"before":b.before.iter().map(observed).collect::<Vec<_>>(),
                "after":b.after.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>()},
        "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(c,v)|json!([c,hex::encode(v.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
            "left":index(left),"right":index(right)})).collect::<Vec<_>>()})
}
fn asset_hash_page_json(page:&catalogue::AssetHashPage<'_>) -> Value {
    json!({"schema":"shieldd-transfer-asset-hash-block-v1","family":"transfer",
        "scope":"balance ASSET_GENERATOR26/1 permutation with exact asset/map-u LCs; native/kernel joins open",
        "slot":0,"role":"asset","level":0,"block":0,"map_input":observed(page.map_input),
        "hash":{"domain":26,"inputs":[observed(&page.hash.asset)],"output":observed(&page.hash.output),
            "blocks":[{"before":page.hash.before.iter().map(observed).collect::<Vec<_>>(),
                "after":page.hash.after.iter().map(observed).collect::<Vec<_>>()}]},
        "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(c,v)|json!([c,hex::encode(v.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,
            "left":index(left),"right":index(right)})).collect::<Vec<_>>()})
}
fn transfer_t4_descriptor(ordinal:usize) -> anyhow::Result<(usize,&'static str,usize,usize)> {
    if ordinal<55 {
        let slot=usize::from(ordinal>=27);let offset=ordinal-if slot==0 {0}else{27};
        let (role,level,block)=match offset {0..=1=>("commitment",0,offset),2=>("nullifier",0,0),
            3..=26=>("state",offset-3,0),27 if slot==1=>("dummy",0,0),_=>anyhow::bail!("input descriptor changed")};
        Ok((slot,role,level,block))
    } else { match ordinal {
        55..=62=>Ok(((ordinal-55)/4,if (ordinal-55)%4<2 {"note"}else{"recovery"},0,(ordinal-55)%2)),
        63=>Ok((0,"asset",0,0)),64=>Ok((0,"roles",0,0)),_=>anyhow::bail!("combined65 ordinal overflow")
    } }
}
fn qualify_transfer_t4_pages(first:&str,repeated:&str,pending:&Value) -> anyhow::Result<()> {
    let pages=pending["pages"].as_array().ok_or_else(||anyhow::anyhow!("missing65 page inventory"))?;
    anyhow::ensure!(pages.len()==65,"combined65 page count");
    let mut input=pending.clone();input["pages"]=json!(&pages[..55]);
    qualify_note_hash_pages(first,repeated,&input)?;
    for ordinal in 55..65 {
        let descriptor=&pages[ordinal];let (slot,role,level,block)=transfer_t4_descriptor(ordinal)?;
        anyhow::ensure!(descriptor.as_object().map(|d|d.len())==Some(6) && descriptor["ordinal"]==ordinal &&
            descriptor["slot"]==slot && descriptor["role"]==role && descriptor["level"]==level && descriptor["block"]==block,
            "combined65 descriptor mismatch");
        let bytes=read_note_hash_page(first,ordinal)?;let repeat=read_note_hash_page(repeated,ordinal)?;
        anyhow::ensure!(bytes==repeat && descriptor["blake3"]==packet_blake3(&bytes),
            "combined65 page repeat/digest mismatch");
        let body:Value=serde_json::from_slice(&bytes)?;
        if ordinal<64 {
            for key in ["slot","role","level","block"] {anyhow::ensure!(body[key]==descriptor[key],"page native role changed");}
            let (schema,domain,arity,width,blocks)=if ordinal==63 {
                ("shieldd-transfer-asset-hash-block-v1",26,1,3,1)
            } else if role=="note" {("shieldd-transfer-note-output-hash-block-v1",15,8,6,2)}
            else {("shieldd-transfer-note-output-hash-block-v1",20,7,6,2)};
            anyhow::ensure!(body["schema"]==schema && body["hash"]["domain"]==domain &&
                body["hash"]["inputs"].as_array().map(Vec::len)==Some(arity) &&
                body["hash"]["blocks"].as_array().map(Vec::len)==Some(blocks),"hash native constructor inventory changed");
            for part in body["hash"]["blocks"].as_array().unwrap() {
                anyhow::ensure!(part["before"].as_array().map(Vec::len)==Some(width) &&
                    part["after"].as_array().map(Vec::len)==Some(width),"hash full checkpoint width changed");
            }
        } else {
            anyhow::ensure!(body["schema"]=="shieldd-transfer-t4-roles-v1" &&
                body["tree"]["schema"]=="shieldd-transfer-note-tree-v1" && body["tree"]["depth"]==24 &&
                body["tree"]["levels"].as_array().map(Vec::len)==Some(48) &&
                body["tree"]["spend"]["schema"]=="shieldd-transfer-note-spend-v1" &&
                body["outputs"]["schema"]=="shieldd-transfer-note-output-v1" &&
                body["outputs"]["outputs"].as_array().map(Vec::len)==Some(2),"combined65 roles inventory changed");
        }
        let mut parts=vec![&body];
        if ordinal==64 {parts.extend([&body["tree"],&body["tree"]["spend"],&body["outputs"]]);}
        for part in parts {
            anyhow::ensure!(part["ordinary_full_ordered_rows_equal"]==false && part["repeated_observations_equal"]==false,
                "combined65 pending flags changed");
            for key in ["relation_digest","domain_size","full_rows","constant_copy"] {
                anyhow::ensure!(part[key]==pending[key],"combined65 full relation identity mismatch");
            }
        }
    }
    Ok(())
}
