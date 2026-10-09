// Future-only EPK fixed pages; qualification compares two ordinary spools plus repeat.
fn capture_epk_fixed_pages(lane_name:&str,slot:usize,prefix:&str)->anyhow::Result<()> {
    use shieldd_sdk_circuits::group::epk_fixed_inspection::Lane;
    use commonware_cryptography::bls12381::primitives::group::Scalar;
    let lane=match lane_name {"recovery"=>Lane::Recovery,"encryption"=>Lane::Encryption,
        _=>anyhow::bail!("EPK fixed unknown lane")};
    let mut count=0;
    let (compiled,copy)=catalogue::inspect_transfer_epk_fixed_pages(lane,slot,|ordinal,page| {
        let report=page.report;
        anyhow::ensure!(ordinal==count && count<8 && report.lane==lane && report.slot==slot &&
            report.window_start==16*ordinal && report.window_count==std::cmp::min(16,126-16*ordinal),"EPK fixed callback order/overflow");
        let native_pair=|point:&[Scalar;2]|point.iter().map(|v|json!({"native":hex::encode(v.encode())})).collect::<Vec<_>>();
        let body=json!({"window_start":report.window_start,"window_count":report.window_count,"total_windows":126,"bit_width":252,
            "lane":lane_name,"slot":slot,"base":native_pair(&report.base),"randomizer":observed(&report.randomizer),
            "inverse":observed(report.inverse.as_ref().ok_or_else(||anyhow::anyhow!("EPK fixed missing inverse"))?),"bits":report.bits.iter().map(index).collect::<Vec<_>>(),"published":pair(&report.published),"output":pair(&report.output),
            "windows":report.windows.iter().map(|w|json!({"index":w.index,"table":w.table.iter().map(native_pair).collect::<Vec<_>>(),
                "points":w.points.iter().map(pair).collect::<Vec<_>>(),"bits":w.bits.iter().map(index).collect::<Vec<_>>(),
                "arithmetic":w.arithmetic.iter().map(observed).collect::<Vec<_>>(),"quotient":w.quotient.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
        anyhow::ensure!(serde_json::to_vec(&body)?.len()<=2*1024*1024,"EPK fixed page JSON exceeds2MiB");
        write_packet_json(prefix,&format!("page{ordinal}.observations.json"),&body)?;count+=1;Ok(())
    })?;
    anyhow::ensure!(count==8 && copy==200692,"incomplete EPK fixed pages/copy");
    let spool=RowSpool::new(&compiled)?;ensure_epk_fixed_original_layout(&spool.shape())?;spool.persist(prefix,"observer")?;drop(compiled);
    let mut pages=Vec::new();
    for ordinal in 0..8 {
        let mut body=read_packet_json(prefix,&format!("page{ordinal}.observations.json"))?;
        let object=body.as_object_mut().ok_or_else(||anyhow::anyhow!("EPK fixed page object"))?;
        for (key,value) in [("schema",json!("shieldd-transfer-epk-fixed-v1")),("family",json!("transfer")),
            ("scope",json!("bounded fixed EPK source roles; row/native claims open")),
            ("relation_digest",json!(hex::encode(spool.digest))),("domain_size",json!(spool.domain)),
            ("full_rows",json!(spool.rows)),("constant_copy",json!(copy)),
            ("ordinary_full_ordered_rows_equal",json!(false)),("repeated_observations_equal",json!(false))] {object.insert(key.into(),value);}
        qualify_epk_fixed_page(&body)?;write_packet_json(prefix,&format!("page{ordinal}.pending.json"),&body)?;
        let bytes=read_epk_fixed_page(prefix,ordinal)?;
        pages.push(json!({"ordinal":ordinal,"window_start":16*ordinal,"window_count":std::cmp::min(16,126-16*ordinal),"blake3":packet_blake3(&bytes)}));
    }
    write_packet_json(prefix,"pending.json",&json!({"schema":"shieldd-transfer-epk-fixed-pages-v1","family":"transfer",
        "scope":"8 bounded fixed EPK pages from one lowering; row/native claims open","lane":lane_name,"slot":slot,
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"pages":pages}))
}
fn read_epk_fixed_page(prefix:&str,ordinal:usize)->anyhow::Result<Vec<u8>> {
    let mut bytes=Vec::new();File::open(format!("{prefix}.page{ordinal}.pending.json"))?.take(2*1024*1024+1).read_to_end(&mut bytes)?;
    anyhow::ensure!(!bytes.is_empty() && bytes.len()<=2*1024*1024,"EPK fixed page byte bound");Ok(bytes)
}
fn qualify_epk_fixed_page(p:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","lane","slot","window_start","window_count",
        "total_windows","bit_width","base","randomizer","inverse","bits","published","output","windows","expressions","nodes"];
    anyhow::ensure!(p.as_object().is_some_and(|p|p.len()==keys.len() && keys.iter().all(|key|p.contains_key(*key))) &&
        p["schema"]=="shieldd-transfer-epk-fixed-v1" && p["family"]=="transfer" &&
        p["scope"]=="bounded fixed EPK source roles; row/native claims open" &&
        p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false &&
        p["relation_digest"]=="16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236" && p["full_rows"]==200770 && p["domain_size"]==262144 && p["constant_copy"]==200692 &&
        p["total_windows"]==126 && p["bit_width"]==252,"EPK fixed closed page/original shape");
    let slots=match p["lane"].as_str() {Some("recovery")=>2,Some("encryption")=>4,_=>anyhow::bail!("EPK fixed lane")};
    anyhow::ensure!(p["slot"].as_u64().is_some_and(|s|s<slots),"EPK fixed slot");
    let start=p["window_start"].as_u64().ok_or_else(||anyhow::anyhow!("EPK fixed start"))? as usize;
    let count=p["window_count"].as_u64().ok_or_else(||anyhow::anyhow!("EPK fixed count"))? as usize;
    anyhow::ensure!(start<126 && (1..=16).contains(&count) && start+count<=126,"EPK fixed window bounds");
    let array=|v:&Value,len:usize|v.as_array().is_some_and(|a|a.len()==len);
    let bits=p["bits"].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed bits"))?;
    let expressions=p["expressions"].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed expressions"))?;
    anyhow::ensure!(bits.len()==252 && expressions.len()<=4096 && p["nodes"].as_array().is_some_and(|a|a.len()<=8192) &&
        array(&p["base"],2) && array(&p["published"],2) && array(&p["output"],2),"EPK fixed role bounds");
    let mut selected=std::collections::BTreeSet::new();let mut terms=0usize;let mut prior_source=None;
    for expression in expressions {
        anyhow::ensure!(expression.as_object().is_some_and(|v|v.len()==2 && v.contains_key("source") && v.contains_key("terms")) &&
            selected.insert(expression["source"].to_string()),"EPK fixed selected source duplicate/shape");
        let handle=expression["source"].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed LC source"))?;
        anyhow::ensure!(handle.len()==2,"EPK fixed LC source arity");
        let tag=handle[0].as_u64().ok_or_else(||anyhow::anyhow!("EPK fixed LC source tag"))?;
        let index=handle[1].as_u64().ok_or_else(||anyhow::anyhow!("EPK fixed LC source index"))?;
        anyhow::ensure!(tag<=2 && index<=u32::MAX as u64 && prior_source.is_none_or(|prior|prior<(tag,index)),"EPK fixed LC source order");
        prior_source=Some((tag,index));
        let lc=expression["terms"].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed LC terms"))?;
        let mut prior_column=None;
        for term in lc {
            let term=term.as_array().ok_or_else(||anyhow::anyhow!("EPK fixed LC term array"))?;
            anyhow::ensure!(term.len()==2,"EPK fixed LC term arity");
            let column=term[0].as_u64().ok_or_else(||anyhow::anyhow!("EPK fixed LC column"))?;
            let coefficient=term[1].as_str().ok_or_else(||anyhow::anyhow!("EPK fixed LC coefficient"))?;
            anyhow::ensure!(column<262144 && column!=200692 && prior_column.is_none_or(|prior|prior<column) &&
                coefficient.len()==64 && coefficient.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) &&
                coefficient<"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001" &&
                coefficient!="0000000000000000000000000000000000000000000000000000000000000000" &&
                (tag!=0 || column==0),"EPK fixed canonical preoutline LC terms");prior_column=Some(column);
        }
        if tag==1 {anyhow::ensure!(expression["terms"]==json!([[index+3,"0000000000000000000000000000000000000000000000000000000000000001"]]),"EPK fixed witness LC identity");}
        terms+=lc.len();
        anyhow::ensure!(terms<=65536,"EPK fixed LC total bound");
    }
    let mut prior_node=None;
    for node in p["nodes"].as_array().unwrap() {
        anyhow::ensure!(node.as_object().is_some_and(|n|n.len()==4 && ["index","multiply","left","right"].iter().all(|k|n.contains_key(*k))) &&
            node["multiply"].is_boolean(),"EPK fixed closed AST node");
        let index=node["index"].as_u64().ok_or_else(||anyhow::anyhow!("EPK fixed AST node index"))?;
        anyhow::ensure!(index<=u32::MAX as u64 && prior_node.is_none_or(|prior|prior<index),"EPK fixed AST node order");prior_node=Some(index);
        for key in ["left","right"] {
            let child=node[key].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed AST child"))?;
            anyhow::ensure!(child.len()==2 && child[0].as_u64().is_some_and(|tag|tag<=2) &&
                child[1].as_u64().is_some_and(|value|value<=u32::MAX as u64 && (child[0]!=2 || value<index)),"EPK fixed AST child topology");
        }
    }
    let source=|v:&Value|->anyhow::Result<()> {
        anyhow::ensure!(v.as_array().is_some_and(|v|v.len()==2 && v[0].as_u64().is_some_and(|k|k<=2) && v[1].as_u64().is_some()) &&
            selected.contains(&v.to_string()),"EPK fixed role missing selected LC");Ok(())
    };
    let observed=|v:&Value|->anyhow::Result<()> {
        let o=v.as_object().ok_or_else(||anyhow::anyhow!("EPK fixed observed object"))?;
        anyhow::ensure!(o.len()==1,"EPK fixed observed shape");
        if let Some(v)=o.get("source") {source(v)} else {
            let v=o.get("native").and_then(Value::as_str).ok_or_else(||anyhow::anyhow!("EPK fixed native encoding"))?;
            anyhow::ensure!(v.len()==64 && v.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) &&
                v<"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001","EPK fixed canonical native value");Ok(())
        }
    };
    let mut distinct=std::collections::BTreeSet::new();for bit in bits {source(bit)?;anyhow::ensure!(bit[0]==1,"EPK fixed bit witness source");anyhow::ensure!(distinct.insert(bit.to_string()),"EPK fixed duplicate bit");}
    observed(&p["randomizer"])?;observed(&p["inverse"])?;
    anyhow::ensure!(p["inverse"]["source"][0]==1,"EPK fixed inverse witness source");
    for key in ["base","published","output"] {for v in p[key].as_array().unwrap() {observed(v)?;}}
    let windows=p["windows"].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed windows"))?;
    anyhow::ensure!(windows.len()==count,"EPK fixed incomplete windows");
    for (offset,w) in windows.iter().enumerate() {
        anyhow::ensure!(w.as_object().is_some_and(|w|w.len()==6 && ["index","table","points","bits","arithmetic","quotient"].iter().all(|k|w.contains_key(*k))) &&
            w["index"]==start+offset && array(&w["table"],4) && array(&w["points"],3) && array(&w["bits"],2) &&
            array(&w["arithmetic"],4) && array(&w["quotient"],6),"EPK fixed window closed shape");
        for (pair_index,b) in w["bits"].as_array().unwrap().iter().enumerate() {anyhow::ensure!(b==&bits[2*(start+offset)+pair_index],"EPK fixed bit pair order");}
        for key in ["table","points"] {for point in w[key].as_array().unwrap() {anyhow::ensure!(array(point,2),"EPK fixed point");for v in point.as_array().unwrap() {observed(v)?;}}}
        for key in ["arithmetic","quotient"] {for v in w[key].as_array().unwrap() {observed(v)?;}}
        anyhow::ensure!(w["quotient"][4]==w["points"][2][0] && w["quotient"][5]==w["points"][2][1],"EPK fixed quotient endpoint");
        if offset>0 {anyhow::ensure!(windows[offset-1]["points"][2]==w["points"][0] && windows[offset-1]["table"][3]==w["table"][0],"EPK fixed point/table chain");}
    }
    if start==0 {anyhow::ensure!(windows[0]["table"][0]==p["base"] && windows[0]["points"][0]==json!([
        {"native":"0000000000000000000000000000000000000000000000000000000000000000"},
        {"native":"0000000000000000000000000000000000000000000000000000000000000001"}]),"EPK fixed initial identity/base");}
    if start+count==126 {anyhow::ensure!(windows.last().unwrap()["points"][2]==p["output"],"EPK fixed final endpoint");}Ok(())
}
fn qualify_epk_fixed_pages(first:&str,repeated:&str,p:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","lane","slot","pages"];
    anyhow::ensure!(p.as_object().is_some_and(|p|p.len()==keys.len() && keys.iter().all(|k|p.contains_key(*k))) &&
        p["schema"]=="shieldd-transfer-epk-fixed-pages-v1" && p["family"]=="transfer" &&
        p["scope"]=="8 bounded fixed EPK pages from one lowering; row/native claims open" &&
        p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false,"EPK fixed closed pending parent");
    let pages=p["pages"].as_array().ok_or_else(||anyhow::anyhow!("EPK fixed descriptors"))?;
    anyhow::ensure!(pages.len()==8,"EPK fixed exacteight pages");let mut previous:Option<Value>=None;
    for (ordinal,d) in pages.iter().enumerate() {
        anyhow::ensure!(d.as_object().is_some_and(|d|d.len()==4 && ["ordinal","window_start","window_count","blake3"].iter().all(|k|d.contains_key(*k))) &&
            d["ordinal"]==ordinal && d["window_start"]==16*ordinal && d["window_count"]==std::cmp::min(16,126-16*ordinal),"EPK fixed descriptor order");
        let bytes=read_epk_fixed_page(first,ordinal)?;
        anyhow::ensure!(bytes==read_epk_fixed_page(repeated,ordinal)? && d["blake3"]==packet_blake3(&bytes),"EPK fixed repeat/page bytes");
        let page:Value=serde_json::from_slice(&bytes)?;qualify_epk_fixed_page(&page)?;
        for key in ["relation_digest","domain_size","full_rows","constant_copy","lane","slot","window_start","window_count"] {
            let expected=if key.starts_with("window_"){&d[key]}else{&p[key]};anyhow::ensure!(&page[key]==expected,"EPK fixed page/parent identity");
        }
        if let Some(prior)=&previous {
            for key in ["base","randomizer","inverse","bits","published","output","lane","slot"] {anyhow::ensure!(page[key]==prior[key],"EPK fixed shared roles");}
            let last=prior["windows"].as_array().unwrap().last().unwrap();
            anyhow::ensure!(last["points"][2]==page["windows"][0]["points"][0] && last["table"][3]==page["windows"][0]["table"][0],"EPK fixed page continuity");
        }previous=Some(page);
    }Ok(())
}
fn ensure_epk_fixed_original_layout(shape:&Value)->anyhow::Result<()> {
    ensure_original_shape(shape)?;
    anyhow::ensure!(shape["source_public"]==json!([[1,22734]]) && shape["source_blocks"]==json!([[[1,6]]]),
        "EPK fixed original public/committed source identity");Ok(())
}

fn capture_epk_all_fixed_pages(prefix:&str)->anyhow::Result<()> {
    use shieldd_sdk_circuits::group::epk_fixed_inspection::Lane;
    use commonware_cryptography::bls12381::primitives::group::Scalar;
    let mut count=0;
    let (compiled,copy)=catalogue::inspect_transfer_epk_all_fixed_pages(|ordinal,page| {
        let report=page.report;
        let lane_name=match report.lane {Lane::Recovery=>"recovery",Lane::Encryption=>"encryption"};let slot=report.slot;
        anyhow::ensure!(ordinal==count && count<48 &&
            shieldd_sdk_circuits::group::epk_fixed_inspection::scope_id(ordinal/8)==Some((report.lane,slot)) &&
            report.window_start==16*(ordinal%8) && report.window_count==std::cmp::min(16,126-16*(ordinal%8)),"EPK all callback scope/order/overflow");
        let native_pair=|point:&[Scalar;2]|point.iter().map(|v|json!({"native":hex::encode(v.encode())})).collect::<Vec<_>>();
        let body=json!({"window_start":report.window_start,"window_count":report.window_count,"total_windows":126,"bit_width":252,
            "lane":lane_name,"slot":slot,"base":native_pair(&report.base),"randomizer":observed(&report.randomizer),
            "inverse":observed(report.inverse.as_ref().ok_or_else(||anyhow::anyhow!("EPK fixed missing inverse"))?),"bits":report.bits.iter().map(index).collect::<Vec<_>>(),"published":pair(&report.published),"output":pair(&report.output),
            "windows":report.windows.iter().map(|w|json!({"index":w.index,"table":w.table.iter().map(native_pair).collect::<Vec<_>>(),
                "points":w.points.iter().map(pair).collect::<Vec<_>>(),"bits":w.bits.iter().map(index).collect::<Vec<_>>(),
                "arithmetic":w.arithmetic.iter().map(observed).collect::<Vec<_>>(),"quotient":w.quotient.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
        anyhow::ensure!(serde_json::to_vec(&body)?.len()<=2*1024*1024,"EPK fixed page JSON exceeds2MiB");
        write_packet_json(prefix,&format!("page{ordinal}.observations.json"),&body)?;count+=1;Ok(())
    })?;
    anyhow::ensure!(count==48 && copy==200692,"incomplete EPK fixed pages/copy");
    let spool=RowSpool::new(&compiled)?;ensure_epk_fixed_original_layout(&spool.shape())?;spool.persist(prefix,"observer")?;drop(compiled);
    let mut pages=Vec::new();let mut scopes=Vec::new();
    for ordinal in 0..48 {
        let mut body=read_packet_json(prefix,&format!("page{ordinal}.observations.json"))?;
        let object=body.as_object_mut().ok_or_else(||anyhow::anyhow!("EPK fixed page object"))?;
        for (key,value) in [("schema",json!("shieldd-transfer-epk-fixed-v1")),("family",json!("transfer")),
            ("scope",json!("bounded fixed EPK source roles; row/native claims open")),
            ("relation_digest",json!(hex::encode(spool.digest))),("domain_size",json!(spool.domain)),
            ("full_rows",json!(spool.rows)),("constant_copy",json!(copy)),
            ("ordinary_full_ordered_rows_equal",json!(false)),("repeated_observations_equal",json!(false))] {object.insert(key.into(),value);}
        qualify_epk_fixed_page(&body)?;write_packet_json(prefix,&format!("page{ordinal}.pending.json"),&body)?;
        let bytes=read_epk_fixed_page(prefix,ordinal)?;
        if ordinal%8==0 {scopes.push(json!({"lane":body["lane"],"slot":body["slot"],"randomizer":body["randomizer"],
            "published":body["published"],"output":body["output"],"inverse":body["inverse"]}));}
        pages.push(json!({"ordinal":ordinal,"window_start":16*(ordinal%8),"window_count":std::cmp::min(16,126-16*(ordinal%8)),"scope_id":ordinal/8,"blake3":packet_blake3(&bytes)}));
    }
    write_packet_json(prefix,"pending.json",&json!({"schema":"shieldd-transfer-epk-all-fixed-pages-v1","family":"transfer",
        "scope":"48 bounded fixed EPK pages for six ordered scopes from one lowering; row/native claims open","scopes":scopes,
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"pages":pages}))
}
fn qualify_epk_all_fixed_pages(first:&str,repeated:&str,p:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","scopes","pages"];
    anyhow::ensure!(p.as_object().is_some_and(|p|p.len()==keys.len() && keys.iter().all(|k|p.contains_key(*k))) &&
        p["schema"]=="shieldd-transfer-epk-all-fixed-pages-v1" && p["family"]=="transfer" &&
        p["scope"]=="48 bounded fixed EPK pages for six ordered scopes from one lowering; row/native claims open" &&
        p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false,
        "EPK all closed pending parent");
    let scopes=p["scopes"].as_array().ok_or_else(||anyhow::anyhow!("EPK all scopes"))?;
    let pages=p["pages"].as_array().ok_or_else(||anyhow::anyhow!("EPK all pages"))?;
    anyhow::ensure!(scopes.len()==6 && pages.len()==48,"EPK all exact6 scopes/48 pages");
    let mut previous:Option<Value>=None;let mut base:Option<Value>=None;
    let mut private=std::collections::BTreeSet::new();
    let mut expressions=std::collections::BTreeMap::new();let mut nodes=std::collections::BTreeMap::new();
    for (ordinal,d) in pages.iter().enumerate() {
        let scope_id=ordinal/8;let local=ordinal%8;
        let lane=if scope_id<2 {"recovery"} else {"encryption"};let slot=if scope_id<2 {scope_id} else {scope_id-2};
        let scope=&scopes[scope_id];
        anyhow::ensure!(scope.as_object().is_some_and(|s|s.len()==6 &&
            ["lane","slot","randomizer","published","output","inverse"].iter().all(|k|s.contains_key(*k))) &&
            scope["lane"]==lane && scope["slot"]==slot,"EPK all exact typed scope order");
        anyhow::ensure!(d.as_object().is_some_and(|d|d.len()==5 &&
            ["ordinal","scope_id","window_start","window_count","blake3"].iter().all(|k|d.contains_key(*k))) &&
            d["ordinal"]==ordinal && d["scope_id"]==scope_id && d["window_start"]==16*local &&
            d["window_count"]==std::cmp::min(16,126-16*local),"EPK all descriptor order");
        let bytes=read_epk_fixed_page(first,ordinal)?;
        anyhow::ensure!(bytes==read_epk_fixed_page(repeated,ordinal)? && d["blake3"]==packet_blake3(&bytes),"EPK all repeat bytes");
        let page:Value=serde_json::from_slice(&bytes)?;qualify_epk_fixed_page(&page)?;
        for key in ["relation_digest","domain_size","full_rows","constant_copy"] {
            anyhow::ensure!(page[key]==p[key],"EPK all ordinary parent identity");
        }
        for key in ["lane","slot","randomizer","published","output","inverse"] {
            anyhow::ensure!(page[key]==scope[key],"EPK all scalar/endpoints/scope correspondence");
        }
        anyhow::ensure!(page["window_start"]==d["window_start"] && page["window_count"]==d["window_count"],"EPK all page bounds");
        if let Some(base)=&base {anyhow::ensure!(page["base"]==*base,"EPK all same generator object");} else {base=Some(page["base"].clone());}
        if local==0 {
            anyhow::ensure!(page["randomizer"]["source"][0]==1,"EPK all scalar witness");
            for value in page["bits"].as_array().unwrap().iter().chain(
                [&page["randomizer"]["source"],&page["inverse"]["source"]]) {
                anyhow::ensure!(private.insert(value.to_string()),"EPK all private scalar/bit/inverse alias");
            }
        } else if let Some(prior)=&previous {
            for key in ["base","randomizer","inverse","bits","published","output","lane","slot"] {
                anyhow::ensure!(page[key]==prior[key],"EPK all shared scope roles");
            }
            let last=prior["windows"].as_array().unwrap().last().unwrap();
            anyhow::ensure!(last["points"][2]==page["windows"][0]["points"][0] &&
                last["table"][3]==page["windows"][0]["table"][0],"EPK all 6x126 crosspage continuity");
        }
        for expression in page["expressions"].as_array().unwrap() {
            let key=expression["source"].to_string();let value=&expression["terms"];
            if let Some(prior)=expressions.insert(key,value.clone()) {anyhow::ensure!(prior==*value,"EPK all samecompile source LC disagreement");}
        }
        for node in page["nodes"].as_array().unwrap() {
            let key=node["index"].to_string();
            if let Some(prior)=nodes.insert(key,node.clone()) {anyhow::ensure!(prior==*node,"EPK all samecompile source AST disagreement");}
        }
        previous=Some(page);
    }Ok(())
}
