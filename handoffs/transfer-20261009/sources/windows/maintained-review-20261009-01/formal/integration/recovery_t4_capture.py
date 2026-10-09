"""New future74 mode; keep retained65 mode byte for byte in the same stage.

Pure source composition. The root owns builds, full ordinary2/repeat capture
qualification and the maintained CLI registration. No active stage is edited.
"""
from .recovery_hash_observer import replace_once
import re


def _function(text,name):
    """Exact top-level function body, skipping quoted strings/comments."""
    starts=list(re.finditer(r'^fn '+re.escape(name)+r'\(',text,re.M))
    if len(starts)>1:raise ValueError('duplicate retained recovery qualifier definition')
    if not starts:return None
    start=starts[0].start();position=text.index('{',starts[0].end());depth=0
    quoted=False;escaped=False;line_comment=False;block_comment=0
    while position<len(text):
        ch=text[position];pair=text[position:position+2]
        if line_comment:
            if ch=='\n':line_comment=False
        elif block_comment:
            if pair=='/*':block_comment+=1;position+=1
            elif pair=='*/':block_comment-=1;position+=1
        elif quoted:
            if escaped:escaped=False
            elif ch=='\\':escaped=True
            elif ch=='"':quoted=False
        elif pair=='//':line_comment=True;position+=1
        elif pair=='/*':block_comment=1;position+=1
        elif ch=='"':quoted=True
        elif ch=='{':depth+=1
        elif ch=='}':
            depth-=1
            if depth==0:return text[start:position+1]
        position+=1
    raise ValueError('unterminated recovery qualifier function')


def _append_qualifier_once(text,fragment,qualifier):
    names=('recovery_t4_descriptor','qualify_recovery_t4_pages')
    pending=qualifier
    for name in names:
        wanted=_function(qualifier,name)
        if wanted is None:raise ValueError('missing maintained recovery qualifier')
        embedded=_function(fragment,name)
        if embedded is not None:
            if embedded!=wanted:raise ValueError('embedded recovery qualifier source drift')
            fragment=fragment.replace(embedded,'',1)
        retained=_function(text,name)
        if retained is not None:
            if retained!=wanted:raise ValueError('retained recovery qualifier source drift')
            pending=pending.replace(wanted,'',1)
    result=text+'\n'+fragment+'\n'+pending
    for name in names:
        if _function(result,name) is None:raise ValueError('missing composed recovery qualifier')
    return result


def catalogue(source,cone_resource):
    if not isinstance(source,bytes) or not isinstance(cone_resource,bytes):raise ValueError('recovery74 source bytes')
    text=source.decode().replace('\r\n','\n')
    # A separate function/types/helper walk permit retaining the old65 include.
    for old,new in [('inspect_transfer_t4_pages','inspect_transfer_t4_recovery_pages'),('TransferT4Page','RecoveryT4Page'),
        ('TransferTreePage','RecoveryTreePage'),('OutputHashPage','RecoveryOutputHashPage'),('AssetHashPage','RecoveryAssetHashPage'),
        ('transfer_hash_page_cone','recovery_transfer_hash_page_cone'),('output_hash_page_cone','recovery_output_hash_page_cone'),
        ('asset_hash_page_cone','recovery_asset_hash_page_cone')]:text=text.replace(old,new)
    text=replace_once(text,'    Asset(RecoveryAssetHashPage<\'a>),',
        "    Asset(RecoveryAssetHashPage<'a>),\n    RecoveryHash(RecoveryHashPage<'a>),\n    RecoveryRoles(RecoveryRolesPage<'a>),")
    text=replace_once(text,'    let _asset_map_capture = crate::map::asset_inspection::begin()?;',
        '    let _asset_map_capture = crate::map::asset_inspection::begin()?;\n    let _capsule_capture = crate::recovery::capsule_inspection::begin()?;\n    let _recovery_hash_capture = crate::recovery::hash_inspection::begin()?;')
    text=replace_once(text,'    let outputs = crate::note::output_inspection::take()?;',
        '''    let outputs = crate::note::output_inspection::take()?;
    let capsules = crate::recovery::capsule_inspection::take()?;
    let recovery_hashes = crate::recovery::hash_inspection::take(&capsules)?;
    for slot in 0..2 {let core=&capsules[slot].core;let output=&outputs.outputs[slot];
        anyhow::ensure!(core.amount==output.note[1] && core.blinding==output.note[0] &&
            core.capsule==output.capsule && core.commitment==output.capsule_commitment &&
            core.payload_key==output.payload_key,"recovery/output actual source roles changed");
    }
    let mut recovery_selected=capsules.iter().flat_map(|capsule|capsule.selected()).collect::<Vec<_>>();
    recovery_selected.sort();recovery_selected.dedup();
    anyhow::ensure!(recovery_selected.len()<=1024,"recovery roles page bound");''')
    text=replace_once(text,'    anyhow::ensure!(pages.len() == 65, "combined65 source inventory changed");',
        '''    anyhow::ensure!(pages.len() == 65, "retained65 prefix inventory changed");
    for hash in &recovery_hashes {pages.push(recovery_hash_page_cone(&c,&capsules,hash)?.0);}
    pages.push(recovery_selected);
    anyhow::ensure!(pages.len()==74,"recovery74 page inventory changed");''')
    text=replace_once(text,'        65,','        74,')
    text=replace_once(text,'            } else {\n                anyhow::ensure!(ordinal == 64,',
        '''            } else if ordinal<73 && ordinal>=65 {
                let hash=&recovery_hashes[ordinal-65];
                let (expected,nodes)=recovery_hash_page_cone(&c,&capsules,hash)?;
                anyhow::ensure!(expected.as_slice()==selected,"recovery hash page LC inventory changed");
                consume(ordinal,RecoveryT4Page::RecoveryHash(RecoveryHashPage {
                    hash,capsules:&capsules,selected,expressions,nodes,
                }))
            } else if ordinal==73 {
                consume(ordinal,RecoveryT4Page::RecoveryRoles(RecoveryRolesPage {capsules:&capsules,selected,expressions}))
            } else {
                anyhow::ensure!(ordinal == 64,''')
    text+='''
#[cfg(feature = "formal-observer")]
pub struct RecoveryRolesPage<'a> {
    pub capsules:&'a [crate::recovery::capsule_inspection::Report;2],
    pub selected:&'a [circuit::CircuitIdx],pub expressions:Vec<Vec<(u32,Scalar)>>,
}
'''
    return (text+'\n'+cone_resource.decode().replace('transfer_hash_page_cone','recovery_transfer_hash_page_cone')).encode()


def exporter(source,roles_resource,hash_resource):
    if not all(isinstance(data,bytes) for data in (source,roles_resource,hash_resource)):raise ValueError('recovery74 exporter bytes')
    text=source.decode().replace('\r\n','\n')
    # Keep only the capture function; generic serializers/qualifier remain the
    # old65 exports. Two typed hash serializers are copied with new type names.
    capture=text[:text.index('\nfn output_roles_json(')]
    def function(name):
        start=text.index('\nfn '+name+'(')+1;end=text.find('\nfn ',start)
        return text[start:] if end<0 else text[start:end]
    typed=function('output_hash_page_json')+'\n'+function('asset_hash_page_json')
    for old,new in [('capture_transfer_t4_pages','capture_transfer_t4_recovery_pages'),('inspect_transfer_t4_pages','inspect_transfer_t4_recovery_pages'),
        ('TransferT4Page','RecoveryT4Page'),('output_hash_page_json','recovery_output_hash_page_json'),
        ('asset_hash_page_json','recovery_asset_hash_page_json')]:capture=capture.replace(old,new)
    for old,new in [('output_hash_page_json','recovery_output_hash_page_json'),('asset_hash_page_json','recovery_asset_hash_page_json'),
        ('catalogue::OutputHashPage','catalogue::RecoveryOutputHashPage'),('catalogue::AssetHashPage','catalogue::RecoveryAssetHashPage')]:typed=typed.replace(old,new)
    capture=capture.replace('count < 65','count < 74').replace('count == 65','count == 74').replace('0..65','0..74')
    capture=replace_once(capture,'            catalogue::RecoveryT4Page::Tree(page) => {',
        '''            catalogue::RecoveryT4Page::RecoveryHash(page) => recovery_hash_page_json(&page),
            catalogue::RecoveryT4Page::RecoveryRoles(page) => recovery_capsule_roles_json(page.capsules,page.selected,&page.expressions),
            catalogue::RecoveryT4Page::Tree(page) => {''')
    capture=capture.replace('transfer_t4_descriptor(ordinal)?','recovery_t4_descriptor(ordinal)?')
    capture=capture.replace('shieldd-transfer-t4-pages-v1','shieldd-transfer-t4-recovery-pages-v1')
    capture=capture.replace('55 input hash +8 output hash +1 asset hash +1 compact roles page from one lowering; native/kernel joins open',
        'retained65 pages plus8 recovery hashes and1 recovery roles page from one lowering; native/kernel joins open')
    return (capture+'\n'+typed+'\n'+roles_resource.decode()+'\n'+hash_resource.decode()).encode()


def instrument_catalogue(data):
    if not isinstance(data,bytes) or b'transfer_t4_recovery_pages_catalogue.rs' in data:raise ValueError('fresh recovery74 catalogue source required')
    return data+b'\n#[cfg(feature = "formal-observer")]\ninclude!("transfer_t4_recovery_pages_catalogue.rs");\n'


def instrument_exporter(data,fragment,qualifier):
    if not all(isinstance(d,bytes) for d in (data,fragment,qualifier)) or b'capture_transfer_t4_recovery_pages' in data:
        raise ValueError('fresh recovery74 exporter source required')
    text=data.decode().replace('\r\n','\n')
    text=replace_once(text,'    let args: Vec<_> = std::env::args().skip(1).collect();',
        '''    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len()==2 && args[0]=="transfer-t4-recovery-pages-spool" {
        return capture_transfer_t4_recovery_pages(&args[1]);
    }''')
    text=replace_once(text,'        Some("shieldd-transfer-t4-pages-v1") |',
        '''        Some("shieldd-transfer-t4-recovery-pages-v1") |
        Some("shieldd-transfer-t4-pages-v1") |''')
    text=replace_once(text,'            if pending["schema"] == "shieldd-transfer-t4-pages-v1" {',
        '''            if pending["schema"] == "shieldd-transfer-t4-recovery-pages-v1" {
                qualify_recovery_t4_pages(first,repeated,&pending)?;
            }
            if pending["schema"] == "shieldd-transfer-t4-pages-v1" {''')
    return _append_qualifier_once(text,fragment.decode().replace('\r\n','\n'),qualifier.decode().replace('\r\n','\n')).encode()
