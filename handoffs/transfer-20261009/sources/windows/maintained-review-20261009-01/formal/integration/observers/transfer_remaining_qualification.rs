// Called only after the existing distinct-four-spool complete row comparison.
fn qualify_remaining_pages(first:&str,repeated:&str,pending:&Value)->anyhow::Result<()> {
    use shieldd_sdk_circuits::transfer::remaining_inspection::{SCOPES,expected_hashes,record_shapes};
    fn closed(value:&Value,keys:&[&str])->bool {
        value.as_object().map(|o|o.len()==keys.len() && keys.iter().all(|k|o.contains_key(*k))).unwrap_or(false)
    }
    fn reference(v:&Value)->anyhow::Result<()> {
        if closed(v,&["source"]) {
            let s=v["source"].as_array().ok_or_else(||anyhow::anyhow!("remaining source array"))?;
            anyhow::ensure!(s.len()==2 && s[0].as_u64().map(|n|n<3)==Some(true)
                && s[1].as_u64().map(|n|n<u64::from(u32::MAX)+1)==Some(true),"remaining source tag/index");
        } else {
            anyhow::ensure!(closed(v,&["native"]),"remaining reference closed shape");
            let text=v["native"].as_str().ok_or_else(||anyhow::anyhow!("remaining native text"))?;
            anyhow::ensure!(text.len()==64 && text.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                && text<"73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffff00000001","remaining canonical native field");
        }
        Ok(())
    }
    anyhow::ensure!(closed(pending,&["schema","family","scope","pages","qualification","semantic_status",
        "relation_digest","domain_size","full_rows","constant_copy","ordinary_full_ordered_rows_equal","repeated_observations_equal"])
        && pending["schema"]=="shieldd-transfer-remaining-source-pages-v1" && pending["family"]=="transfer"
        && pending["qualification"]==false && pending["ordinary_full_ordered_rows_equal"]==false
        && pending["repeated_observations_equal"]==false && pending["semantic_status"]==
        "typed source/LC observations only; ordinary/repeat/kernel/native joins open","remaining closed pending manifest");
    let scope=pending["scope"].as_str().ok_or_else(||anyhow::anyhow!("remaining scope"))?;
    anyhow::ensure!(SCOPES.contains(&scope),"remaining unsupported scope");
    let order=["sender","receiver","volume","audit-sender","audit-receiver","encryption","routing","statement"];
    let roster=order.iter().flat_map(|owner|expected_hashes(owner).into_iter().map(move |(d,a)|(*owner,d,a))).collect::<Vec<_>>();
    anyhow::ensure!(roster.len()==98,"remaining exact source hash roster changed");
    let mut wanted=vec![(None,0usize)];
    for (index,(owner,_,arity)) in roster.iter().enumerate() {
        if *owner==scope {let rate=if *arity<=2 {2} else {5};
            wanted.extend((0..arity.div_ceil(rate)).map(|block|(Some(index),block)));}
    }
    let descriptors=pending["pages"].as_array().ok_or_else(||anyhow::anyhow!("remaining page inventory"))?;
    anyhow::ensure!(descriptors.len()==wanted.len() && wanted.len()<=74,"remaining exact component page count");
    let mut records=None;let mut calls=None;
    for (ordinal,(descriptor,(hash,block))) in descriptors.iter().zip(wanted).enumerate() {
        anyhow::ensure!(closed(descriptor,&["ordinal","suffix","bytes","blake3","hash","block"])
            && descriptor["ordinal"].as_u64()==Some(ordinal as u64) && descriptor["block"].as_u64()==Some(block as u64)
            && descriptor["hash"]==json!(hash) && descriptor["suffix"]==format!("pending-page-{ordinal:03}.json"),
            "remaining closed ordered page descriptor");
        let bytes=read_note_hash_page(first,ordinal)?;let repeat=read_note_hash_page(repeated,ordinal)?;
        anyhow::ensure!(bytes==repeat && bytes.len()<=4*1024*1024 && descriptor["bytes"].as_u64()==Some(bytes.len() as u64)
            && descriptor["blake3"]==packet_blake3(&bytes),"remaining exact first/repeat page bytes");
        let page:Value=serde_json::from_slice(&bytes)?;
        anyhow::ensure!(closed(&page,&["schema","family","scope","ordinal","qualification","ordinary_full_ordered_rows_equal",
            "repeated_observations_equal","records","calls","hash","nodes","expressions"])
            && page["schema"]=="shieldd-transfer-remaining-source-page-v1" && page["family"]=="transfer"
            && page["scope"]==scope && page["ordinal"].as_u64()==Some(ordinal as u64) && page["qualification"]==false
            && page["ordinary_full_ordered_rows_equal"]==false && page["repeated_observations_equal"]==false,
            "remaining closed pending page");
        if ordinal==0 {
            let rs=page["records"].as_array().ok_or_else(||anyhow::anyhow!("remaining exact records"))?;
            let mut shapes=Vec::new();
            for r in rs {
                anyhow::ensure!(closed(r,&["scope","tag","ordinal","values"]),"remaining closed record");
                let owner=r["scope"].as_str().ok_or_else(||anyhow::anyhow!("remaining record scope"))?;
                let tag=r["tag"].as_str().ok_or_else(||anyhow::anyhow!("remaining record tag"))?;
                let index=r["ordinal"].as_u64().ok_or_else(||anyhow::anyhow!("remaining record ordinal"))?;
                let values=r["values"].as_array().ok_or_else(||anyhow::anyhow!("remaining record values"))?;
                anyhow::ensure!(index<=31 && !values.is_empty() && values.len()<=1024,"remaining record bounds");
                for value in values {reference(value)?;}
                shapes.push((owner,tag,index as usize,values.len()));
            }
            shapes.sort();anyhow::ensure!(shapes==record_shapes(),"remaining exact role shape inventory");
            let hs=page["calls"].as_array().ok_or_else(||anyhow::anyhow!("remaining exact calls"))?;
            anyhow::ensure!(hs.len()==roster.len(),"remaining hash count");
            for (h,(owner,domain,arity)) in hs.iter().zip(&roster) {
                anyhow::ensure!(closed(h,&["scope","domain","inputs","output","blocks"])
                    && h["scope"]==*owner && h["domain"].as_u64()==Some(u64::from(*domain)),"remaining closed hash scope/domain");
                let inputs=h["inputs"].as_array().ok_or_else(||anyhow::anyhow!("remaining hash inputs"))?;
                let blocks=h["blocks"].as_array().ok_or_else(||anyhow::anyhow!("remaining hash blocks"))?;
                let (width,rate)=if *arity<=2 {(3,2)} else {(6,5)};
                anyhow::ensure!(inputs.len()==*arity && blocks.len()==arity.div_ceil(rate),"remaining exact arity/block count");
                for v in inputs {reference(v)?;}reference(&h["output"])?;
                for b in blocks {
                    anyhow::ensure!(closed(b,&["before","after"]),"remaining closed checkpoint");
                    for key in ["before","after"] {
                        let lanes=b[key].as_array().ok_or_else(||anyhow::anyhow!("remaining checkpoint lanes"))?;
                        anyhow::ensure!(lanes.len()==width,"remaining checkpoint width");
                        for v in lanes {reference(v)?;}
                    }
                }
                anyhow::ensure!(blocks.last().map(|b|&b["after"][1])==Some(&h["output"]),"remaining output lane/source");
            }
            records=Some(page["records"].clone());calls=Some(page["calls"].clone());
        }
        anyhow::ensure!(records.as_ref()==Some(&page["records"]) && calls.as_ref()==Some(&page["calls"]),
            "remaining shared record/call report changed across pages");
        if let Some(index)=hash {
            let mut call=page["calls"][index].clone();let o=call.as_object_mut().ok_or_else(||anyhow::anyhow!("remaining selected hash"))?;
            o.insert("index".into(),json!(index));o.insert("block".into(),json!(block));
            anyhow::ensure!(page["hash"]==call,"remaining selected global hash changed");
        } else {anyhow::ensure!(page["hash"].is_null() && page["nodes"]==json!([]),"remaining role page claims no permutation");}
        anyhow::ensure!(page["nodes"].as_array().map(|a|a.len()<=16384)==Some(true)
            && page["expressions"].as_array().map(|a|!a.is_empty() && a.len()<=4096)==Some(true),"remaining node/LC bounds");
    }
    Ok(())
}
