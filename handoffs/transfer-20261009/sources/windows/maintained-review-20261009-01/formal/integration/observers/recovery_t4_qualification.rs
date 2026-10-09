// Future74 closed page inventory; qualified_metadata retains the full four
// ordinary spool comparison before dispatching this bounded page qualifier.
fn recovery_t4_descriptor(ordinal:usize)->anyhow::Result<(usize,&'static str,usize,usize)> {
    if ordinal<65 {return transfer_t4_descriptor(ordinal)}
    if ordinal<73 {
        let offset=ordinal-65;let role=["secret","confirmation","amount-stream","blinding-stream"][offset%4];
        return Ok((offset/4,role,0,0));
    }
    anyhow::ensure!(ordinal==73,"recovery74 descriptor overflow");Ok((0,"recovery-roles",0,0))
}
fn qualify_recovery_t4_pages(first:&str,repeated:&str,pending:&Value)->anyhow::Result<()> {
    let pages=pending["pages"].as_array().ok_or_else(||anyhow::anyhow!("missing recovery74 page inventory"))?;
    anyhow::ensure!(pages.len()==74,"recovery74 exact page count");
    let mut retained=pending.clone();retained["pages"]=json!(&pages[..65]);
    qualify_transfer_t4_pages(first,repeated,&retained)?;
    let roles:Value=serde_json::from_slice(&read_note_hash_page(first,73)?)?;
    let old:Value=serde_json::from_slice(&read_note_hash_page(first,64)?)?;
    let capsules=roles["capsules"].as_array().ok_or_else(||anyhow::anyhow!("missing two capsules"))?;
    let outputs=old["outputs"]["outputs"].as_array().ok_or_else(||anyhow::anyhow!("missing accepted output roles"))?;
    anyhow::ensure!(roles.as_object().map(|o|o.len())==Some(11) &&
        roles["schema"]=="shieldd-transfer-recovery-capsule-roles-v1" && roles["family"]=="transfer" &&
        roles["scope"]=="two output recovery source roles including both EPK inverses; scalar/group/hash/native joins open" &&
        capsules.len()==2 && outputs.len()==2 && roles["expressions"].as_array().map(|v|v.len()<=1024)==Some(true),
        "recovery exact roles schema/inventory/handle bound");
    for slot in 0..2 {
        let c=&capsules[slot];let out=&outputs[slot];
        anyhow::ensure!(c.as_object().map(|o|o.len())==Some(19) && c["capsule"]==out["capsule"] &&
            c["commitment"]==out["capsule_commitment"] && c["payload_key"]==out["payload_key"] &&
            c["amount"]==out["note"][1] && c["blinding"]==out["note"][0] &&
            c["bits"].as_array().map(Vec::len)==Some(252),"recovery exact output source links changed");
    }
    for ordinal in 65..74 {
        let descriptor=&pages[ordinal];let (slot,role,level,block)=recovery_t4_descriptor(ordinal)?;
        anyhow::ensure!(descriptor.as_object().map(|o|o.len())==Some(6) && descriptor["ordinal"]==ordinal &&
            descriptor["slot"]==slot && descriptor["role"]==role && descriptor["level"]==level && descriptor["block"]==block,
            "recovery exact page descriptor changed");
        let bytes=read_note_hash_page(first,ordinal)?;let repeat=read_note_hash_page(repeated,ordinal)?;
        anyhow::ensure!(bytes==repeat && descriptor["blake3"]==packet_blake3(&bytes),"recovery repeated page identity mismatch");
        let body:Value=serde_json::from_slice(&bytes)?;
        anyhow::ensure!(body["ordinary_full_ordered_rows_equal"]==false && body["repeated_observations_equal"]==false,
            "recovery pending flags changed");
        for key in ["relation_digest","domain_size","full_rows","constant_copy"] {
            anyhow::ensure!(body[key]==pending[key],"recovery full ordinary relation identity mismatch");
        }
        if ordinal==73 {continue}
        let c=&capsules[slot];let (domain,width,inputs,output)=match role {
            "secret"=>(11,3,c["shared"].clone(),c["secret"].clone()),
            "confirmation"=>(21,6,json!([c["seed"],c["capsule"][0],c["capsule"][1],c["capsule"][3]]),c["computed_confirmation"].clone()),
            "amount-stream"=>(10,3,json!([c["seed"],{"native":format!("{:064x}",0)}]),c["amount_stream"].clone()),
            "blinding-stream"=>(10,3,json!([c["seed"],{"native":format!("{:064x}",1)}]),c["blinding_stream"].clone()),
            _=>anyhow::bail!("unknown recovery role"),
        };
        anyhow::ensure!(body.as_object().map(|o|o.len())==Some(16) &&
            body["schema"]=="shieldd-transfer-recovery-hash-block-v1" && body["family"]=="transfer" &&
            body["scope"]=="one recovery secret11/2 confirmation21/4 or stream10/2 permutation with exact two capsule source roles; native/kernel joins open" &&
            body["slot"]==slot && body["role"]==role && body["level"]==0 && body["block"]==0 &&
            body["hash"]["domain"]==domain && body["hash"]["inputs"]==inputs && body["hash"]["output"]==output &&
            body["hash"]["blocks"].as_array().map(Vec::len)==Some(1) &&
            body["hash"]["blocks"][0]["before"].as_array().map(Vec::len)==Some(width) &&
            body["hash"]["blocks"][0]["after"].as_array().map(Vec::len)==Some(width) &&
            body["hash"]["blocks"][0]["after"][1]==output &&
            body["expressions"].as_array().map(|v|v.len()<=4096)==Some(true) &&
            body["nodes"].as_array().map(|v|v.len()<=16384)==Some(true),"recovery native framing/source/selection mismatch");
    }
    Ok(())
}
