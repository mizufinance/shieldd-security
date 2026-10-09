// Future-only balance blinding fixed pages; qualification compares two ordinary spools plus repeat.
fn capture_balance_blinding_fixed_pages(prefix:&str)->anyhow::Result<()> {
    use commonware_cryptography::bls12381::primitives::group::Scalar;
    let mut count=0;
    let (compiled,copy)=catalogue::inspect_transfer_balance_blinding_fixed_pages(|ordinal,page| {
        let report=page.report;
        anyhow::ensure!(ordinal==count && count<8 &&
            report.window_start==16*ordinal && report.window_count==std::cmp::min(16,126-16*ordinal),"balance blinding fixed callback order/overflow");
        let native_pair=|point:&[Scalar;2]|point.iter().map(|v|json!({"native":hex::encode(v.encode())})).collect::<Vec<_>>();
        let body=json!({"window_start":report.window_start,"window_count":report.window_count,"total_windows":126,"bit_width":252,
            "generator":"VALUE_BLINDING","base":native_pair(&report.base),"blinding":observed(&report.blinding),
            "bits":report.bits.iter().map(index).collect::<Vec<_>>(),"output":pair(&report.output),
            "windows":report.windows.iter().map(|w|json!({"index":w.index,"table":w.table.iter().map(native_pair).collect::<Vec<_>>(),
                "points":w.points.iter().map(pair).collect::<Vec<_>>(),"bits":w.bits.iter().map(index).collect::<Vec<_>>(),
                "arithmetic":w.arithmetic.iter().map(observed).collect::<Vec<_>>(),"quotient":w.quotient.iter().map(observed).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),
                "terms":terms.iter().map(|(column,coefficient)|json!([column,hex::encode(coefficient.encode())])).collect::<Vec<_>>() })).collect::<Vec<_>>(),
            "nodes":page.nodes.iter().map(|(node,multiply,left,right)|json!({"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()});
        anyhow::ensure!(serde_json::to_vec(&body)?.len()<=2*1024*1024,"balance blinding fixed page JSON exceeds2MiB");
        write_packet_json(prefix,&format!("page{ordinal}.observations.json"),&body)?;count+=1;Ok(())
    })?;
    anyhow::ensure!(count==8 && copy==200692,"incomplete balance blinding fixed pages/copy");
    let spool=RowSpool::new(&compiled)?;ensure_balance_blinding_original_layout(&spool.shape())?;spool.persist(prefix,"observer")?;drop(compiled);
    let mut pages=Vec::new();
    for ordinal in 0..8 {
        let mut body=read_packet_json(prefix,&format!("page{ordinal}.observations.json"))?;
        let object=body.as_object_mut().ok_or_else(||anyhow::anyhow!("balance blinding fixed page object"))?;
        for (key,value) in [("schema",json!("shieldd-transfer-balance-blinding-fixed-v1")),("family",json!("transfer")),
            ("scope",json!("bounded VALUE_BLINDING fixed source roles; row/native claims open")),
            ("relation_digest",json!(hex::encode(spool.digest))),("domain_size",json!(spool.domain)),
            ("full_rows",json!(spool.rows)),("constant_copy",json!(copy)),
            ("ordinary_full_ordered_rows_equal",json!(false)),("repeated_observations_equal",json!(false))] {object.insert(key.into(),value);}
        qualify_balance_blinding_fixed_page(&body)?;write_packet_json(prefix,&format!("page{ordinal}.pending.json"),&body)?;
        let bytes=read_balance_blinding_fixed_page(prefix,ordinal)?;
        pages.push(json!({"ordinal":ordinal,"window_start":16*ordinal,"window_count":std::cmp::min(16,126-16*ordinal),"blake3":packet_blake3(&bytes)}));
    }
    write_packet_json(prefix,"pending.json",&json!({"schema":"shieldd-transfer-balance-blinding-fixed-pages-v1","family":"transfer",
        "scope":"8 bounded VALUE_BLINDING fixed pages from one lowering; row/native claims open","generator":"VALUE_BLINDING",
        "relation_digest":hex::encode(spool.digest),"domain_size":spool.domain,"full_rows":spool.rows,"constant_copy":copy,
        "ordinary_full_ordered_rows_equal":false,"repeated_observations_equal":false,"pages":pages}))
}
fn read_balance_blinding_fixed_page(prefix:&str,ordinal:usize)->anyhow::Result<Vec<u8>> {
    let mut bytes=Vec::new();File::open(format!("{prefix}.page{ordinal}.pending.json"))?.take(2*1024*1024+1).read_to_end(&mut bytes)?;
    anyhow::ensure!(!bytes.is_empty() && bytes.len()<=2*1024*1024,"balance blinding fixed page byte bound");Ok(bytes)
}
fn qualify_balance_blinding_fixed_page(p:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","generator","window_start","window_count",
        "total_windows","bit_width","base","blinding","bits","output","windows","expressions","nodes"];
    anyhow::ensure!(p.as_object().is_some_and(|p|p.len()==keys.len() && keys.iter().all(|key|p.contains_key(*key))) &&
        p["schema"]=="shieldd-transfer-balance-blinding-fixed-v1" && p["family"]=="transfer" &&
        p["scope"]=="bounded VALUE_BLINDING fixed source roles; row/native claims open" &&
        p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false &&
        p["relation_digest"]=="16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236" && p["full_rows"]==200770 && p["domain_size"]==262144 && p["constant_copy"]==200692 &&
        p["total_windows"]==126 && p["bit_width"]==252,"balance blinding fixed closed page/original shape");
    anyhow::ensure!(p["generator"]=="VALUE_BLINDING","balance blinding generator marker");
    let start=p["window_start"].as_u64().ok_or_else(||anyhow::anyhow!("balance blinding fixed start"))? as usize;
    let count=p["window_count"].as_u64().ok_or_else(||anyhow::anyhow!("balance blinding fixed count"))? as usize;
    anyhow::ensure!(start<126 && (1..=16).contains(&count) && start+count<=126,"balance blinding fixed window bounds");
    let array=|v:&Value,len:usize|v.as_array().is_some_and(|a|a.len()==len);
    let bits=p["bits"].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed bits"))?;
    let expressions=p["expressions"].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed expressions"))?;
    anyhow::ensure!(bits.len()==252 && expressions.len()<=4096 && p["nodes"].as_array().is_some_and(|a|a.len()<=8192) &&
        array(&p["base"],2) && array(&p["output"],2),"balance blinding fixed role bounds");
    let mut selected=std::collections::BTreeSet::new();let mut terms=0usize;let mut prior_source=None;
    for expression in expressions {
        anyhow::ensure!(expression.as_object().is_some_and(|v|v.len()==2 && v.contains_key("source") && v.contains_key("terms")) &&
            selected.insert(expression["source"].to_string()),"balance blinding fixed selected source duplicate/shape");
        let handle=expression["source"].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC source"))?;
        anyhow::ensure!(handle.len()==2,"balance blinding fixed LC source arity");
        let tag=handle[0].as_u64().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC source tag"))?;
        let index=handle[1].as_u64().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC source index"))?;
        anyhow::ensure!(tag<=2 && index<=u32::MAX as u64 && prior_source.is_none_or(|prior|prior<(tag,index)),"balance blinding fixed LC source order");
        prior_source=Some((tag,index));
        let lc=expression["terms"].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC terms"))?;
        let mut prior_column=None;
        for term in lc {
            let term=term.as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC term array"))?;
            anyhow::ensure!(term.len()==2,"balance blinding fixed LC term arity");
            let column=term[0].as_u64().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC column"))?;
            let coefficient=term[1].as_str().ok_or_else(||anyhow::anyhow!("balance blinding fixed LC coefficient"))?;
            anyhow::ensure!(column<262144 && column!=200692 && prior_column.is_none_or(|prior|prior<column) &&
                coefficient.len()==64 && coefficient.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) &&
                coefficient<"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001" &&
                coefficient!="0000000000000000000000000000000000000000000000000000000000000000" &&
                (tag!=0 || column==0),"balance blinding fixed canonical preoutline LC terms");prior_column=Some(column);
        }
        if tag==1 {anyhow::ensure!(expression["terms"]==json!([[index+3,"0000000000000000000000000000000000000000000000000000000000000001"]]),"balance blinding fixed witness LC identity");}
        terms+=lc.len();
        anyhow::ensure!(terms<=65536,"balance blinding fixed LC total bound");
    }
    let mut prior_node=None;
    for node in p["nodes"].as_array().unwrap() {
        anyhow::ensure!(node.as_object().is_some_and(|n|n.len()==4 && ["index","multiply","left","right"].iter().all(|k|n.contains_key(*k))) &&
            node["multiply"].is_boolean(),"balance blinding fixed closed AST node");
        let index=node["index"].as_u64().ok_or_else(||anyhow::anyhow!("balance blinding fixed AST node index"))?;
        anyhow::ensure!(index<=u32::MAX as u64 && prior_node.is_none_or(|prior|prior<index),"balance blinding fixed AST node order");prior_node=Some(index);
        for key in ["left","right"] {
            let child=node[key].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed AST child"))?;
            anyhow::ensure!(child.len()==2 && child[0].as_u64().is_some_and(|tag|tag<=2) &&
                child[1].as_u64().is_some_and(|value|value<=u32::MAX as u64 && (child[0]!=2 || value<index)),"balance blinding fixed AST child topology");
        }
    }
    let source=|v:&Value|->anyhow::Result<()> {
        anyhow::ensure!(v.as_array().is_some_and(|v|v.len()==2 && v[0].as_u64().is_some_and(|k|k<=2) && v[1].as_u64().is_some()) &&
            selected.contains(&v.to_string()),"balance blinding fixed role missing selected LC");Ok(())
    };
    let observed=|v:&Value|->anyhow::Result<()> {
        let o=v.as_object().ok_or_else(||anyhow::anyhow!("balance blinding fixed observed object"))?;
        anyhow::ensure!(o.len()==1,"balance blinding fixed observed shape");
        if let Some(v)=o.get("source") {source(v)} else {
            let v=o.get("native").and_then(Value::as_str).ok_or_else(||anyhow::anyhow!("balance blinding fixed native encoding"))?;
            anyhow::ensure!(v.len()==64 && v.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) &&
                v<"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001","balance blinding fixed canonical native value");Ok(())
        }
    };
    let mut distinct=std::collections::BTreeSet::new();for bit in bits {source(bit)?;anyhow::ensure!(bit[0]==1,"balance blinding fixed bit witness source");anyhow::ensure!(distinct.insert(bit.to_string()),"balance blinding fixed duplicate bit");}
    observed(&p["blinding"])?;
    anyhow::ensure!(p["blinding"]["source"][0]==1,"balance blinding scalar witness source");
    for key in ["base","output"] {for v in p[key].as_array().unwrap() {observed(v)?;}}
    anyhow::ensure!(p["base"].as_array().unwrap().iter().all(|v|v["native"].is_string()),"balance blinding native parameter base");
    let windows=p["windows"].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed windows"))?;
    anyhow::ensure!(windows.len()==count,"balance blinding fixed incomplete windows");
    for (offset,w) in windows.iter().enumerate() {
        anyhow::ensure!(w.as_object().is_some_and(|w|w.len()==6 && ["index","table","points","bits","arithmetic","quotient"].iter().all(|k|w.contains_key(*k))) &&
            w["index"]==start+offset && array(&w["table"],4) && array(&w["points"],3) && array(&w["bits"],2) &&
            array(&w["arithmetic"],4) && array(&w["quotient"],6),"balance blinding fixed window closed shape");
        for (pair_index,b) in w["bits"].as_array().unwrap().iter().enumerate() {anyhow::ensure!(b==&bits[2*(start+offset)+pair_index],"balance blinding fixed bit pair order");}
        for key in ["table","points"] {for point in w[key].as_array().unwrap() {anyhow::ensure!(array(point,2),"balance blinding fixed point");for v in point.as_array().unwrap() {observed(v)?;}}}
        for key in ["arithmetic","quotient"] {for v in w[key].as_array().unwrap() {observed(v)?;}}
        anyhow::ensure!(w["quotient"][4]==w["points"][2][0] && w["quotient"][5]==w["points"][2][1],"balance blinding fixed quotient endpoint");
        if offset>0 {anyhow::ensure!(windows[offset-1]["points"][2]==w["points"][0] && windows[offset-1]["table"][3]==w["table"][0],"balance blinding fixed point/table chain");}
    }
    if start==0 {anyhow::ensure!(windows[0]["table"][0]==p["base"] && windows[0]["points"][0]==json!([
        {"native":"0000000000000000000000000000000000000000000000000000000000000000"},
        {"native":"0000000000000000000000000000000000000000000000000000000000000001"}]),"balance blinding fixed initial identity/base");}
    if start+count==126 {anyhow::ensure!(windows.last().unwrap()["points"][2]==p["output"],"balance blinding fixed final endpoint");}Ok(())
}
fn qualify_balance_blinding_fixed_pages(first:&str,repeated:&str,p:&Value)->anyhow::Result<()> {
    let keys=["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","generator","pages"];
    anyhow::ensure!(p.as_object().is_some_and(|p|p.len()==keys.len() && keys.iter().all(|k|p.contains_key(*k))) &&
        p["schema"]=="shieldd-transfer-balance-blinding-fixed-pages-v1" && p["family"]=="transfer" &&
        p["scope"]=="8 bounded VALUE_BLINDING fixed pages from one lowering; row/native claims open" &&
        p["generator"]=="VALUE_BLINDING" &&
        p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false,"balance blinding fixed closed pending parent");
    let pages=p["pages"].as_array().ok_or_else(||anyhow::anyhow!("balance blinding fixed descriptors"))?;
    anyhow::ensure!(pages.len()==8,"balance blinding fixed exacteight pages");let mut previous:Option<Value>=None;
    for (ordinal,d) in pages.iter().enumerate() {
        anyhow::ensure!(d.as_object().is_some_and(|d|d.len()==4 && ["ordinal","window_start","window_count","blake3"].iter().all(|k|d.contains_key(*k))) &&
            d["ordinal"]==ordinal && d["window_start"]==16*ordinal && d["window_count"]==std::cmp::min(16,126-16*ordinal),"balance blinding fixed descriptor order");
        let bytes=read_balance_blinding_fixed_page(first,ordinal)?;
        anyhow::ensure!(bytes==read_balance_blinding_fixed_page(repeated,ordinal)? && d["blake3"]==packet_blake3(&bytes),"balance blinding fixed repeat/page bytes");
        let page:Value=serde_json::from_slice(&bytes)?;qualify_balance_blinding_fixed_page(&page)?;
        for key in ["relation_digest","domain_size","full_rows","constant_copy","generator","window_start","window_count"] {
            let expected=if key.starts_with("window_"){&d[key]}else{&p[key]};anyhow::ensure!(&page[key]==expected,"balance blinding fixed page/parent identity");
        }
        if let Some(prior)=&previous {
            for key in ["base","blinding","bits","output","generator"] {anyhow::ensure!(page[key]==prior[key],"balance blinding fixed shared roles");}
            let last=prior["windows"].as_array().unwrap().last().unwrap();
            anyhow::ensure!(last["points"][2]==page["windows"][0]["points"][0] && last["table"][3]==page["windows"][0]["table"][0],"balance blinding fixed page continuity");
        }previous=Some(page);
    }Ok(())
}
fn ensure_balance_blinding_original_layout(shape:&Value)->anyhow::Result<()> {
    ensure_original_shape(shape)?;
    anyhow::ensure!(shape["source_public"]==json!([[1,22734]]) && shape["source_blocks"]==json!([[[1,6]]]),
        "balance blinding fixed original public/committed source identity");Ok(())
}
