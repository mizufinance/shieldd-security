// Append to existing exporter only; pending flags require its full ordinary2/repeat qualifier.
fn capture_balance_variable(start: usize,count: usize,prefix: &str) -> anyhow::Result<()> {
    let catalogue::BalanceVariableInspection { compiled,report,selected,expressions,constant_copy,nodes } =
        catalogue::inspect_transfer_balance_variable(start,count)?;
    let spool=RowSpool::new(&compiled)?; ensure_original_shape(&spool.shape())?;
    anyhow::ensure!(constant_copy==200692,"balance variable constant copy changed");
    spool.persist(prefix,"observer")?; drop(compiled);
    let metadata=json!({"schema":"shieldd-transfer-balance-variable-v1","family":"transfer",
        "scope":"bounded balance129 variable-loop observation; actual row/group/native joins open",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,
        "constant_copy":constant_copy,"ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,
        "window_start":report.window_start,"window_count":report.window_count,"total_windows":65,"bit_width":129,
        "negative":observed(&report.negative),"magnitude":observed(&report.magnitude),
        "base":pair(&report.base),"twice":pair(&report.twice),"triple":pair(&report.triple),
        "bits":report.bits.iter().map(index).collect::<Vec<_>>(),"output":pair(&report.output),
        "precompute_quotients":report.precompute_quotients.iter().map(|q|q.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "windows":report.windows.iter().map(|w|json!({"index":w.index,"points":w.points.iter().map(pair).collect::<Vec<_>>(),
            "bits":w.bits.iter().map(observed).collect::<Vec<_>>(),
            "quotients":w.quotients.iter().map(|q|q.iter().map(observed).collect::<Vec<_>>()).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({"source":index(source),
            "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
        "nodes":nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
    write_packet_json(prefix,"pending.json",&metadata)
}
fn qualify_balance_variable(p: &Value) -> anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","window_start","window_count","total_windows",
        "bit_width","negative","magnitude","base","twice","triple","bits","output","precompute_quotients","windows","expressions","nodes"];
    let object=p.as_object().ok_or_else(||anyhow::anyhow!("balance variable object required"))?;
    anyhow::ensure!(object.len()==keys.len() && keys.iter().all(|k|object.contains_key(*k)) &&
        p["schema"]=="shieldd-transfer-balance-variable-v1" && p["family"]=="transfer" && p["scope"]=="bounded balance129 variable-loop observation; actual row/group/native joins open" &&
        p["bit_width"]==129 && p["total_windows"]==65 && p["ordinary_full_ordered_rows_equal"]==false &&
        p["repeated_observations_equal"]==false,"balance variable closed pending scope");
    let start=p["window_start"].as_u64().ok_or_else(||anyhow::anyhow!("balance variable start"))?;
    let count=p["window_count"].as_u64().ok_or_else(||anyhow::anyhow!("balance variable count"))?;
    anyhow::ensure!(start<65 && (1..=16).contains(&count) && start+count<=65,"balance variable65/16 bounds");
    let bits=p["bits"].as_array().ok_or_else(||anyhow::anyhow!("balance variable bits"))?;
    anyhow::ensure!(bits.len()==129 && bits.iter().all(|bit|bit.as_array().is_some_and(|b|b.len()==2 && b[0]==1 && b[1].as_u64().is_some())),"balance variable129 source bits");
    let distinct:std::collections::BTreeSet<_>=bits.iter().map(|bit|bit.to_string()).collect();
    anyhow::ensure!(distinct.len()==129,"balance variable duplicate bits");
    let windows=p["windows"].as_array().ok_or_else(||anyhow::anyhow!("balance variable windows"))?;
    let pre=p["precompute_quotients"].as_array().ok_or_else(||anyhow::anyhow!("balance variable precompute"))?;
    anyhow::ensure!(windows.len()==count as usize && pre.len()==2 && pre.iter().all(|q|q.as_array().is_some_and(|q|q.len()==6)),"balance variable bounded quotient inventory");
    let pair_ok=|value:&Value|value.as_array().is_some_and(|pair|pair.len()==2);
    anyhow::ensure!(["base","twice","triple","output"].iter().all(|key|pair_ok(&p[*key])) &&
        json!([pre[0][4].clone(),pre[0][5].clone()])==p["twice"] &&
        json!([pre[1][4].clone(),pre[1][5].clone()])==p["triple"],"balance variable shared table quotient outputs");
    for (offset,window) in windows.iter().enumerate() {
        let index=start+offset as u64;let low=128-2*index;
        let points=window["points"].as_array().ok_or_else(||anyhow::anyhow!("balance variable points"))?;
        let quotients=window["quotients"].as_array().ok_or_else(||anyhow::anyhow!("balance variable quotients"))?;
        let high=if index==0 { json!({"native":"0000000000000000000000000000000000000000000000000000000000000000"}) }
            else { json!({"source":bits[(low+1) as usize]}) };
        anyhow::ensure!(window.as_object().is_some_and(|w|w.len()==4 && ["index","points","bits","quotients"].iter().all(|k|w.contains_key(*k))) &&
            window["index"]==index && points.len()==5 && points.iter().all(pair_ok) && quotients.len()==3 &&
            quotients.iter().all(|q|q.as_array().is_some_and(|q|q.len()==6)) &&
            window["bits"]==json!([{"source":bits[low as usize]},high]),"balance variable exact reversed padded window");
        for (q,point) in quotients.iter().zip([1,2,4]) {
            anyhow::ensure!(json!([q[4].clone(),q[5].clone()])==points[point],"balance variable quotient point roles");
        }
        if offset>0 { anyhow::ensure!(points[0]==windows[offset-1]["points"][4],"balance variable chain"); }
    }
    if start==0 { anyhow::ensure!(windows[0]["points"][0]==json!([
        {"native":"0000000000000000000000000000000000000000000000000000000000000000"},
        {"native":"0000000000000000000000000000000000000000000000000000000000000001"}]),"balance variable initial identity"); }
    if start+count==65 { anyhow::ensure!(windows.last().unwrap()["points"][4]==p["output"],"balance variable final endpoint"); }
    anyhow::ensure!(p["expressions"].as_array().is_some_and(|e|e.len()<=4096) &&
        p["nodes"].as_array().is_some_and(|n|n.len()<=8192),"balance variable source bounds");
    let expressions=p["expressions"].as_array().unwrap();
    let mut selected=std::collections::BTreeSet::new();
    let mut term_count=0usize;
    for expression in expressions {
        anyhow::ensure!(expression.as_object().is_some_and(|e|e.len()==2 && e.contains_key("source") && e.contains_key("terms")),"balance variable expression shape");
        anyhow::ensure!(selected.insert(expression["source"].to_string()),"balance variable duplicate selected source");
        let terms=expression["terms"].as_array().ok_or_else(||anyhow::anyhow!("balance variable LC terms"))?;
        term_count+=terms.len(); anyhow::ensure!(term_count<=65536,"balance variable total LC term bound");
    }
    let check_observed=|value:&Value|->anyhow::Result<()> {
        let object=value.as_object().ok_or_else(||anyhow::anyhow!("balance variable observed value"))?;
        anyhow::ensure!(object.len()==1,"balance variable observed shape");
        if let Some(source)=object.get("source") {
            anyhow::ensure!(source.as_array().is_some_and(|s|s.len()==2 && s[0].as_u64().is_some_and(|t|t<=2) && s[1].as_u64().is_some()) &&
                selected.contains(&source.to_string()),"balance variable role missing selected LC");
        } else {
            let native=object.get("native").and_then(Value::as_str).ok_or_else(||anyhow::anyhow!("balance variable native value"))?;
            anyhow::ensure!(native.len()==64 && native.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),"balance variable native encoding");
            anyhow::ensure!(native<"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001","balance variable noncanonical native");
        }
        Ok(())
    };
    for bit in bits { check_observed(&json!({"source":bit}))?; }
    for key in ["negative","magnitude"] { check_observed(&p[key])?; }
    for key in ["base","twice","triple","output"] { for value in p[key].as_array().unwrap() { check_observed(value)?; } }
    for quotient in pre { for value in quotient.as_array().unwrap() { check_observed(value)?; } }
    for window in windows {
        for point in window["points"].as_array().unwrap() { for value in point.as_array().unwrap() { check_observed(value)?; } }
        for value in window["bits"].as_array().unwrap() { check_observed(value)?; }
        for quotient in window["quotients"].as_array().unwrap() { for value in quotient.as_array().unwrap() { check_observed(value)?; } }
    }
    Ok(())
}
