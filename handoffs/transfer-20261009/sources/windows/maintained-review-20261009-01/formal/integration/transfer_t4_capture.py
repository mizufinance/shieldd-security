"""Fresh-only 65-page source composition; retained 55-page operation unchanged.

This composes maintained Rust resources in a diagnostic copy. It neither builds
nor accepts a capture. The existing full ordered ordinary2/repeat qualifier is
required by the added exporter dispatch.
"""


def _replace(text,old,new):
    if text.count(old)!=1:raise ValueError('combined65 exact source anchor drift')
    return text.replace(old,new)


def catalogue(source,cone_resource):
    if not isinstance(source,bytes) or not isinstance(cone_resource,bytes):raise ValueError('combined65 source bytes')
    text=source.decode().replace('\r\n','\n')
    text=text.replace('NoteT4Page','TransferT4Page').replace('NoteTreePage','TransferTreePage').replace(
        'inspect_transfer_note_t4_pages','inspect_transfer_t4_pages')
    text=_replace(text,"    pub spends: &'a crate::note::spend_inspection::Report,", "    pub spends: &'a crate::note::spend_inspection::Report,\n    pub outputs: &'a crate::note::output_inspection::Report,\n    pub tree_handles: &'a [circuit::CircuitIdx],")
    text=_replace(text,"    Tree(TransferTreePage<'a>),", "    Tree(TransferTreePage<'a>),\n    Output(OutputHashPage<'a>),\n    Asset(AssetHashPage<'a>),")
    text=_replace(text,'    let _tree_capture = crate::tree::note_inspection::begin()?;', '''    let _tree_capture = crate::tree::note_inspection::begin()?;
    let _output_capture = crate::note::output_inspection::begin()?;
    let _output_hash_capture = crate::note::output_hash_inspection::begin()?;
    let _asset_hash_capture = crate::hash::asset_hash_inspection::begin()?;
    let _asset_map_capture = crate::map::asset_inspection::begin()?;''')
    text=_replace(text,'    let levels = crate::tree::note_inspection::take()?;', '''    let levels = crate::tree::note_inspection::take()?;
    let outputs = crate::note::output_inspection::take()?;
    let output_hashes = crate::note::output_hash_inspection::take(&outputs)?;
    let asset_hash = crate::hash::asset_hash_inspection::take()?;
    let asset_map = crate::map::asset_inspection::take()?;
    anyhow::ensure!(asset_hash.asset == asset_map.asset && asset_hash.output == asset_map.hash &&
        asset_map.values[0] == asset_map.hash, "asset hash/map u source boundary changed");
    anyhow::ensure!(asset_hash.asset == spends.spends[0].shared.asset &&
        outputs.outputs.iter().all(|output| output.note[2] == asset_hash.asset),
        "input/output/balance asset source changed");
    let mut output_jobs = Vec::new();
    for hash in output_hashes {
        for block in 0..2 { let mut job = hash.clone(); job.block = block; output_jobs.push(job); }
    }
    anyhow::ensure!(output_jobs.len() == 8, "output eight permutation inventory changed");''')
    text=_replace(text,'    let tree_selected: Vec<_> = tree_selected.into_iter().collect();','''    let tree_handles: Vec<_> = tree_selected.iter().copied().collect();
    tree_selected.extend(outputs.selected());
    let tree_selected: Vec<_> = tree_selected.into_iter().collect();''')
    text=_replace(text,'    pages.push(tree_selected);','''    for hash in &output_jobs { pages.push(output_hash_page_cone(&c, &outputs, hash)?.0); }
    pages.push(asset_hash_page_cone(&c, &asset_hash)?.0);
    pages.push(tree_selected);
    anyhow::ensure!(pages.len() == 65, "combined65 source inventory changed");''')
    text=_replace(text,'        56,','        65,')
    text=_replace(text,'            } else {\n                consume(','''            } else if ordinal < 63 {
                let hash = &output_jobs[ordinal-55];
                let (expected, nodes) = output_hash_page_cone(&c, &outputs, hash)?;
                anyhow::ensure!(expected.as_slice() == selected, "output page inventory changed");
                consume(ordinal, TransferT4Page::Output(OutputHashPage {
                    hash, outputs: &outputs, selected, expressions, nodes,
                }))
            } else if ordinal == 63 {
                let (expected, nodes) = asset_hash_page_cone(&c, &asset_hash)?;
                anyhow::ensure!(expected.as_slice() == selected, "asset page inventory changed");
                consume(ordinal, TransferT4Page::Asset(AssetHashPage {
                    hash: &asset_hash, map_input: &asset_map.values[0], selected, expressions, nodes,
                }))
            } else {
                anyhow::ensure!(ordinal == 64, "combined65 roles ordinal changed");
                consume(''')
    text=_replace(text,'                        spends: &spends,','                        spends: &spends,\n                        outputs: &outputs,\n                        tree_handles: &tree_handles,')
    return (text+'\n'+cone_resource.decode().replace('\r\n','\n')).encode()


def exporter(source,serialization):
    """Reuse the maintained page writer and unchanged input-page serialization."""
    if not isinstance(source,bytes) or not isinstance(serialization,bytes):raise ValueError('combined65 exporter bytes')
    text=source.decode().replace('\r\n','\n')
    # Only the capture function is reused. The bounded qualifier is supplied by
    # the maintained serialization resource and reuses the old55 qualifier.
    text=text[:text.index('\nfn qualify_note_t4_pages(')]
    text=text.replace('capture_note_t4_pages','capture_transfer_t4_pages').replace(
        'inspect_transfer_note_t4_pages','inspect_transfer_t4_pages').replace('NoteT4Page','TransferT4Page')
    text=text.replace('count < 56','count < 65').replace('count == 56','count == 65').replace('0..56','0..65')
    text=_replace(text,'            catalogue::TransferT4Page::Tree(page) => {','''            catalogue::TransferT4Page::Output(page) => output_hash_page_json(&page),
            catalogue::TransferT4Page::Asset(page) => asset_hash_page_json(&page),
            catalogue::TransferT4Page::Tree(page) => {''')
    text=_replace(text,'                json!({"schema":"shieldd-transfer-note-tree-v1"','                let tree = json!({"schema":"shieldd-transfer-note-tree-v1"')
    # Restrict the tree LC inventory to its original handles; outputs receive
    # their own closed inventory in the same compact roles page.
    anchor='"expressions":page.selected.iter().zip(&page.expressions).map(|(source,terms)|json!({"source":index(source),'
    at=text.index('let tree = json!');before,tree=text[:at],text[at:]
    tree=_replace(tree,anchor,'"expressions":page.selected.iter().zip(&page.expressions).filter(|(source,_)|page.tree_handles.contains(source)).map(|(source,terms)|json!({"source":index(source),')
    text=before+tree
    text=_replace(text,'"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()}})\n            }',
        '''"index":node,"multiply":multiply,"left":index(left),"right":index(right)})).collect::<Vec<_>>()}});
                json!({"schema":"shieldd-transfer-t4-roles-v1","family":"transfer",
                    "scope":"two spend/output roles and 48 tree levels; actual row/native joins open",
                    "tree":tree,"outputs":output_roles_json(page.outputs,page.selected,&page.expressions)})
            }''')
    start=text.index('        if ordinal == 55 {');end=text.index('        write_packet_json(prefix, &format!("page{ordinal}.pending.json")',start)
    text=text[:start]+'''        if ordinal == 64 {
            for pointer in ["/tree", "/tree/spend", "/outputs"] {
                let part = body.pointer_mut(pointer).ok_or_else(||anyhow::anyhow!("missing combined roles part"))?;
                for (key,value) in identity.as_object().unwrap() {
                    part.as_object_mut().unwrap().insert(key.clone(),value.clone());
                }
            }
        }
'''+text[end:]
    start=text.index('        pages.push(if ordinal<55');end=text.index('\n    }\n    let mut manifest',start)
    text=text[:start]+'''        let (slot,role,level,block) = transfer_t4_descriptor(ordinal)?;
        pages.push(json!({"ordinal":ordinal,"slot":slot,"role":role,"level":level,"block":block,
            "blake3":packet_blake3(&bytes)}));'''+text[end:]
    text=text.replace('shieldd-transfer-note-t4-pages-v1','shieldd-transfer-t4-pages-v1').replace(
        '55 hash pages plus one two-spend/48-tree LC page from one lowering; native/kernel joins open',
        '55 input hash +8 output hash +1 asset hash +1 compact roles page from one lowering; native/kernel joins open')
    return (text+'\n'+serialization.decode().replace('\r\n','\n')).encode()


def instrument_catalogue(data):
    if not isinstance(data,bytes) or b'transfer_t4_pages_catalogue.rs' in data:
        raise ValueError('fresh combined65 catalogue source required')
    return data+b'\n#[cfg(feature = "formal-observer")]\ninclude!("transfer_t4_pages_catalogue.rs");\n'


def instrument_exporter(data,fragment):
    if not isinstance(data,bytes) or not isinstance(fragment,bytes) or b'fn capture_transfer_t4_pages(' in data:
        raise ValueError('fresh combined65 exporter source required')
    newline='\r\n' if b'\r\n' in data else '\n';text=data.decode().replace('\r\n','\n')
    text=_replace(text,'    let args: Vec<_> = std::env::args().skip(1).collect();', '''    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() == 2 && args[0] == "transfer-t4-pages-spool" {
        return capture_transfer_t4_pages(&args[1]);
    }''')
    text=_replace(text,'        Some("shieldd-transfer-note-t4-pages-v1") => {','''        Some("shieldd-transfer-t4-pages-v1") |
        Some("shieldd-transfer-note-t4-pages-v1") => {
            if pending["schema"] == "shieldd-transfer-t4-pages-v1" {
                qualify_transfer_t4_pages(first,repeated,&pending)?;
            }''')
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()
