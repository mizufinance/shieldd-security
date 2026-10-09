// Future-only five bounded pages from the existing one-compile spool runner.
fn capture_balance_variable_pages(prefix: &str) -> anyhow::Result<()> {
    let mut count=0;
    let (compiled,copy)=catalogue::inspect_transfer_balance_variable_pages(|ordinal,page| {
        let report=page.report;
        anyhow::ensure!(ordinal==count && count<5 && report.window_start==16*ordinal &&
            report.window_count==std::cmp::min(16,65-16*ordinal),"balance variable page callback order/overflow");
        let body=json!({"window_start":report.window_start,"window_count":report.window_count,"total_windows":65,"bit_width":129,
            "negative":observed(&report.negative),"magnitude":observed(&report.magnitude),
            "base":pair(&report.base),"twice":pair(&report.twice),"triple":pair(&report.triple),
            "bits":report.bits.iter().map(index).collect::<Vec<_>>(),"output":pair(&report.output),
            "precompute_quotients":report.precompute_quotients.iter().map(|q|q.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "windows":report.windows.iter().map(|w|json!({"index":w.index,"points":w.points.iter().map(pair).collect::<Vec<_>>(),
                "bits":w.bits.iter().map(observed).collect::<Vec<_>>(),
                "quotients":w.quotients.iter().map(|q|q.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
        anyhow::ensure!(serde_json::to_vec(&body)?.len()<=2*1024*1024,"balance variable page JSON exceeds2MiB");
        write_packet_json(prefix,&format!("page{ordinal}.observations.json"),&body)?;
        count+=1;Ok(()) // This cone/LC/JSON page is discarded before next callback.
    })?;
    anyhow::ensure!(count==5 && copy==200692,"incomplete balance variable pages/copy");
    let spool=RowSpool::new(&compiled)?;ensure_original_shape(&spool.shape())?;
    spool.persist(prefix,"observer")?;drop(compiled);
    let mut pages=Vec::new();
    for ordinal in 0..5 {
        let mut body=read_packet_json(prefix,&format!("page{ordinal}.observations.json"))?;
        let object=body.as_object_mut().ok_or_else(||anyhow::anyhow!("balance variable page object required"))?;
        for (key,value) in [
            ("schema",json!("shieldd-transfer-balance-variable-v1")),("family",json!("transfer")),
            ("scope",json!("bounded balance129 variable-loop observation; actual row/group/native joins open")),
            ("relation_digest",json!(hex::encode(spool.digest))),("domain_size",json!(spool.domain)),
            ("full_rows",json!(spool.rows)),("constant_copy",json!(copy)),
            ("ordinary_full_ordered_rows_equal",json!(false)),("repeated_observations_equal",json!(false))] {
            object.insert(key.into(),value);
        }
        qualify_balance_variable(&body)?;
        write_packet_json(prefix,&format!("page{ordinal}.pending.json"),&body)?;
        let bytes=read_balance_variable_page(prefix,ordinal)?;
        pages.push(json!({"ordinal":ordinal,"window_start":16*ordinal,"window_count":std::cmp::min(16,65-16*ordinal),"blake3":packet_blake3(&bytes)}));
    }
    // Truncated callbacks cannot enter qualification: only successful complete
    // lowering and allfive exact pending pages create the parent manifest.
    write_packet_json(prefix,"pending.json",&json!({"schema":"shieldd-transfer-balance-variable-pages-v1","family":"transfer",
        "scope":"5 bounded balance129 window pages from one lowering; group/native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"pages":pages}))
}
fn read_balance_variable_page(prefix: &str,ordinal:usize) -> anyhow::Result<Vec<u8>> {
    let mut bytes=Vec::new();File::open(format!("{prefix}.page{ordinal}.pending.json"))?
        .take(2*1024*1024+1).read_to_end(&mut bytes)?;
    anyhow::ensure!(!bytes.is_empty() && bytes.len()<=2*1024*1024,"balance variable page byte bound");Ok(bytes)
}
fn qualify_balance_variable_pages(first:&str,repeated:&str,pending:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","pages"];
    let object=pending.as_object().ok_or_else(||anyhow::anyhow!("balance variable pages object required"))?;
    anyhow::ensure!(object.len()==keys.len() && keys.iter().all(|key|object.contains_key(*key)) &&
        pending["schema"]=="shieldd-transfer-balance-variable-pages-v1" && pending["family"]=="transfer" &&
        pending["scope"]=="5 bounded balance129 window pages from one lowering; group/native joins open" &&
        pending["ordinary_full_ordered_rows_equal"]==false && pending["repeated_observations_equal"]==false,
        "balance variable pages closed pending scope");
    let descriptors=pending["pages"].as_array().ok_or_else(||anyhow::anyhow!("balance variable descriptors required"))?;
    anyhow::ensure!(descriptors.len()==5,"balance variable exactfive pages");
    let mut previous:Option<Value>=None;
    for (ordinal,descriptor) in descriptors.iter().enumerate() {
        anyhow::ensure!(descriptor.as_object().is_some_and(|d|d.len()==4 &&
            ["ordinal","window_start","window_count","blake3"].iter().all(|key|d.contains_key(*key))) &&
            descriptor["ordinal"]==ordinal && descriptor["window_start"]==16*ordinal &&
            descriptor["window_count"]==std::cmp::min(16,65-16*ordinal),"balance variable descriptor order/bounds");
        let bytes=read_balance_variable_page(first,ordinal)?;
        anyhow::ensure!(bytes==read_balance_variable_page(repeated,ordinal)? && descriptor["blake3"]==packet_blake3(&bytes),
            "balance variable repeated page/digest mismatch");
        let page:Value=serde_json::from_slice(&bytes)?;qualify_balance_variable(&page)?;
        for key in ["relation_digest","domain_size","full_rows","constant_copy","window_start","window_count"] {
            let expected=if key.starts_with("window_"){&descriptor[key]}else{&pending[key]};
            anyhow::ensure!(&page[key]==expected,"balance variable page/parent identity");
        }
        if let Some(prior)=&previous {
            for key in ["negative","magnitude","base","twice","triple","bits","output","precompute_quotients"] {
                anyhow::ensure!(page[key]==prior[key],"balance variable shared source roles changed");
            }
            anyhow::ensure!(prior["windows"].as_array().unwrap().last().unwrap()["points"][4]==page["windows"][0]["points"][0],
                "balance variable page point continuity");
        }
        previous=Some(page); // Only one bounded parsed predecessor remains.
    }
    Ok(())
}
