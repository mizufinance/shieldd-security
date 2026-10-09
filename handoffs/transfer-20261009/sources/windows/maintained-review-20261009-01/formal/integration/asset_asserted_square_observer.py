"""Fresh child overlay for the two exact asserted squares, no compiler changes.

Their source AST remains captured. Their operands/targets have actual compiler
LCs; the square outputs deliberately do not. Independent typed ingress must
find the original base-squared equals target row before emitting evidence.
"""
from .asset_map_observer import _source
from .recovery_hash_observer import replace_once
from .recovery_t4_capture import _function


def compose(overlays):
    """Pure three-file child of the retained full runtime overlay inventory."""
    result=dict(overlays)
    prefix='crates/crypto/circuits/'
    changes={prefix+'src/asset_map_catalogue.rs':catalogue,
             prefix+'src/asset_nonidentity_catalogue.rs':catalogue,
             prefix+'examples/transfer-ownership-inspection.rs':exporter}
    if any(path not in result or not isinstance(result[path],bytes) for path in changes):
        raise ValueError('retained map/nonidentity/exporter source required')
    for path,upgrade in changes.items():result[path]=upgrade(result[path])
    return result


def catalogue(data):
    text, newline = _source(data)
    text = replace_once(text, '    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,',
        '    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,\n'
        '    pub asserted_squares: Vec<(circuit::CircuitIdx, circuit::CircuitIdx, circuit::CircuitIdx)>,')
    anchor = '    let mut pending: Vec<_> = selected.iter().copied().collect();'
    text = replace_once(text, anchor, '''    // The ordinary lowerer fuses these square outputs with their assertions.
    // Selecting either output would request an LC which does not exist.
    let source = |v: &Observed| match v {
        Observed::Source(i) => Ok(*i),
        _ => Err(anyhow::anyhow!("asserted square requires actual source")),
    };
    let asserted_squares = vec![
        (source(&report.qr[0])?, source(&report.values[9])?, source(&report.qr[1])?),
        (source(&report.constraint_products[0])?, source(&report.values[12])?, source(&report.values[11])?),
    ];
    anyhow::ensure!(asserted_squares[0].0 != asserted_squares[1].0, "asserted square alias");
    for (square, base, target) in &asserted_squares {
        let CircuitIdx::Node(node) = square else { anyhow::bail!("asserted square node required"); };
        let (multiply, left, right) = c.inspect_node(*node)
            .ok_or_else(|| anyhow::anyhow!("missing asserted square AST"))?;
        anyhow::ensure!(multiply && left == *base && right == *base,
            "asserted square source operation changed");
        selected.remove(square);
        selected.extend([*base, *target]);
    }
    let mut pending: Vec<_> = selected.iter().copied()
        .chain(asserted_squares.iter().map(|s| s.0)).collect();''')
    text = replace_once(text, '                selected.extend([index,left,right]);', '''                if !asserted_squares.iter().any(|s| s.0 == index) {
                    selected.extend([index,left,right]);
                }''')
    text = replace_once(text, '            for child in [left, right] {', '''            for child in [left, right] {
                anyhow::ensure!(!asserted_squares.iter().any(|s| s.0 == child),
                    "asserted square reused as source operand");''')
    text = replace_once(text, 'expressions, constant_copy, nodes })',
                        'expressions, constant_copy, nodes, asserted_squares })')
    return text.replace('\n', newline).encode()


def _capture(body, kind):
    text = replace_once(body, 'constant_copy, nodes }', 'constant_copy, nodes, asserted_squares }')
    text = replace_once(text, f'shieldd-transfer-asset-{kind}-v1', f'shieldd-transfer-asset-{kind}-v2')
    text = replace_once(text, '        "nodes":nodes.iter()', '''        "asserted_squares":asserted_squares.iter().map(|(square,base,target)|
            json!({"square":{"source":index(square)},"base":{"source":index(base)},
                "target":{"source":index(target)}})).collect::<Vec<_>>(),
        "nodes":nodes.iter()''')
    return text


def exporter(data):
    """Preserve all unrelated functions, modes and full four-spool qualification."""
    text, newline = _source(data)
    for kind in ('map', 'nonidentity'):
        name = 'capture_asset_' + kind
        body = _function(text, name)
        if body is None: raise ValueError('retained asset capture required')
        text = replace_once(text, body, _capture(body, kind))
    # Existing v1 remains admissible; v2 adds one closed, ordered companion.
    text = replace_once(text, '        Some("shieldd-transfer-asset-nonidentity-v1") |',
        '        Some("shieldd-transfer-asset-nonidentity-v2") |\n'
        '        Some("shieldd-transfer-asset-map-v2") |\n'
        '        Some("shieldd-transfer-asset-nonidentity-v1") |')
    text = replace_once(text, '            if pending["schema"] == "shieldd-transfer-asset-nonidentity-v1" {',
        '            if pending["schema"] == "shieldd-transfer-asset-map-v2" ||\n'
        '                pending["schema"] == "shieldd-transfer-asset-nonidentity-v2" {\n'
        '                qualify_asset_asserted_squares(&pending)?;\n'
        '            }\n'
        '            if pending["schema"] == "shieldd-transfer-asset-nonidentity-v1" ||\n'
        '                pending["schema"] == "shieldd-transfer-asset-nonidentity-v2" {')
    # Nonidentity qualifier rechecks the entire old map inventory unchanged.
    original = _function(text, 'qualify_asset_nonidentity')
    if original is None: raise ValueError('retained asset qualifier required')
    body = original
    body = replace_once(body, '    let keys=[', '    let mut keys=vec![')
    body = replace_once(body, '    let object=p.as_object()',
        '    if p["schema"]=="shieldd-transfer-asset-nonidentity-v2" { keys.push("asserted_squares"); }\n'
        '    let object=p.as_object()')
    body = replace_once(body, 'p["schema"]=="shieldd-transfer-asset-nonidentity-v1" &&',
        '(p["schema"]=="shieldd-transfer-asset-nonidentity-v1" || p["schema"]=="shieldd-transfer-asset-nonidentity-v2") &&')
    text = replace_once(text, original, body)
    text += '\n' + _QUALIFIER
    return text.replace('\n', newline).encode()


_QUALIFIER = '''// Companion validation runs only after the original four-spool comparison.
fn qualify_asset_asserted_squares(p:&Value)->anyhow::Result<()> {
    let mut keys=vec!["schema","family","scope","relation_digest","domain_size","full_rows","constant_copy",
        "ordinary_full_ordered_rows_equal","repeated_observations_equal","asset","hash","values","y_bits",
        "cofactor","cofactor_aux","constraint_products","qr","canonical","expressions","nodes","asserted_squares"];
    if p["schema"]=="shieldd-transfer-asset-nonidentity-v2" { keys.push("nonidentity"); }
    anyhow::ensure!(p.as_object().map(|o|o.len()==keys.len() && keys.iter().all(|k|o.contains_key(*k))).unwrap_or(false)
        && (p["schema"]=="shieldd-transfer-asset-map-v2" || p["schema"]=="shieldd-transfer-asset-nonidentity-v2")
        && p["family"]=="transfer" && p["scope"]=="one balance asset-map source boundary; actual rows/hash/native/codec joins open"
        && p["ordinary_full_ordered_rows_equal"]==false && p["repeated_observations_equal"]==false,
        "asserted square closed pending schema");
    let squares=p["asserted_squares"].as_array()
        .ok_or_else(||anyhow::anyhow!("asserted squares required"))?;
    anyhow::ensure!(squares.len()==2,"exactly two asserted squares required");
    let expected=[(&p["qr"][0],&p["values"][9],&p["qr"][1]),
        (&p["constraint_products"][0],&p["values"][12],&p["values"][11])];
    let expressions=p["expressions"].as_array().ok_or_else(||anyhow::anyhow!("asset expressions required"))?;
    let nodes=p["nodes"].as_array().ok_or_else(||anyhow::anyhow!("asset nodes required"))?;
    for (entry,(square,base,target)) in squares.iter().zip(expected) {
        anyhow::ensure!(entry.as_object().map(|o|o.len()==3 && ["square","base","target"].iter().all(|k|o.contains_key(*k))).unwrap_or(false)
            && &entry["square"]==square && &entry["base"]==base && &entry["target"]==target,
            "asserted square role correspondence");
        let s=&square["source"];let b=&base["source"];let t=&target["source"];
        anyhow::ensure!(s[0]==2 && s[1].as_u64().is_some() && b[0]==1,
            "asserted square source types");
        anyhow::ensure!(!expressions.iter().any(|e|&e["source"]==s) &&
            expressions.iter().filter(|e|&e["source"]==b).count()==1 &&
            expressions.iter().filter(|e|&e["source"]==t).count()==1,
            "asserted square has operands/target LCs only");
        anyhow::ensure!(nodes.iter().filter(|n|n["index"]==s[1] && n["multiply"]==true && &n["left"]==b && &n["right"]==b).count()==1 &&
            !nodes.iter().any(|n|&n["left"]==s || &n["right"]==s),
            "asserted square exact AST and no output reuse");
    }
    anyhow::ensure!(squares[0]["square"]!=squares[1]["square"],"asserted square alias");
    Ok(())
}
'''
