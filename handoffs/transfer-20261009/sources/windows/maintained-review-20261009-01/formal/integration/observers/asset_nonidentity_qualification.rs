// Runs after full ordinary1/ordinary2/observer/repeat row comparison.
fn qualify_asset_nonidentity(p:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","asset","hash","nonidentity",
        "values","y_bits","cofactor","cofactor_aux","constraint_products","qr","canonical","expressions","nodes"];
    let object=p.as_object().ok_or_else(||anyhow::anyhow!("asset nonidentity object required"))?;
    anyhow::ensure!(object.len()==keys.len() && keys.iter().all(|k|object.contains_key(*k)),"asset nonidentity closed schema");
    anyhow::ensure!(p["schema"]=="shieldd-transfer-asset-nonidentity-v1" && p["family"]=="transfer" &&
        p["scope"]=="one balance asset-map source boundary; actual rows/hash/native/codec joins open" &&
        p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false,"asset nonidentity pending scope");
    let n=&p["nonidentity"];
    anyhow::ensure!(n.as_object().map(|o|o.len()==4 && ["asset","hash","generator","inverse"].iter().all(|k|o.contains_key(*k))).unwrap_or(false),"asset nonidentity roles schema");
    anyhow::ensure!(n["asset"]==p["asset"] && n["hash"]==p["hash"] &&
        n["generator"]==p["cofactor"][3] && p["cofactor"].as_array().map(|v|v.len()==4).unwrap_or(false) &&
        n["generator"].as_array().map(|v|v.len()==2).unwrap_or(false),"asset generator exact map/output source links");
    let inverse=&n["inverse"];
    anyhow::ensure!(inverse.as_object().map(|o|o.len()==1 && o.contains_key("source")).unwrap_or(false) &&
        inverse["source"].as_array().map(|i|i.len()==2 && i[0]==1 && i[1].as_u64().is_some()).unwrap_or(false),"actual asset inverse witness source required");
    let expressions=p["expressions"].as_array().ok_or_else(||anyhow::anyhow!("asset selected expressions required"))?;
    anyhow::ensure!(expressions.len()<=4096 && expressions.iter().filter(|e|e["source"]==inverse["source"]).count()==1 &&
        expressions.iter().all(|e|e.as_object().map(|o|o.len()==2 && o.contains_key("source") && o.contains_key("terms")).unwrap_or(false)),"actual inverse LC inventory/shape");
    let mut selected=std::collections::BTreeSet::new();let mut terms=0usize;
    for e in expressions {let encoded=serde_json::to_string(&e["source"])?;
        anyhow::ensure!(selected.insert(encoded),"duplicate asset selected source");
        let row=e["terms"].as_array().ok_or_else(||anyhow::anyhow!("asset LC terms required"))?;terms+=row.len();
        anyhow::ensure!(terms<=65536,"asset LC term bound");
    }
    for role in [&n["asset"],&n["hash"],&n["generator"][0],&n["generator"][1],inverse] {
        let i=role.get("source").ok_or_else(||anyhow::anyhow!("asset nonidentity requires actual source roles"))?;
        anyhow::ensure!(selected.contains(&serde_json::to_string(i)?),"asset nonidentity source missing LC");
    }
    anyhow::ensure!(p["nodes"].as_array().map(|v|v.len()<=16384).unwrap_or(false),"asset nonidentity cone bound");
    Ok(())
}
