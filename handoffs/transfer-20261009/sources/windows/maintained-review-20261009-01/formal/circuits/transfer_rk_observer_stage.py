"""Prepare a fresh source packet for the existing exporter, never a capture.

The active runtime/exporter inventories are read only. A caller must stage and
build this packet separately; its manifest records identities, not semantics.
"""
import hashlib
import json
import re
import tempfile
from pathlib import Path
from .transfer_relation import RelationError


def prepare(destination, runtime_root, formal_root):
    destination, runtime, formal = map(Path,(destination,runtime_root,formal_root))
    if destination.exists():raise RelationError('RK stage destination must be fresh')
    originals={}; generated={}
    def read(root,path):
        data=(root/path).read_bytes()
        originals[str(root/path)]=hashlib.sha256(data).hexdigest()
        return data.decode('utf8').replace('\r\n','\n')
    def replace_once(source,before,after):
        if source.count(before) != 1:raise RelationError('RK staging hook source shape mismatch')
        return source.replace(before,after,1)
    group='crates/crypto/circuits/src/group.rs'
    source=read(runtime,group)
    generated['runtime/'+group]=replace_once(source,'pub mod fixed_inspection;',
        'pub mod fixed_inspection;\n#[cfg(feature = "formal-observer")]\npub mod rk_inspection;')
    recorder='crates/crypto/circuits/src/group/inspection.rs'
    source=read(runtime,recorder)
    generated['runtime/'+recorder]=replace_once(source,'pub(crate) fn scope() -> Option<Scope> {\n',
        'pub(crate) fn scope() -> Option<Scope> {\n'
        '    if super::rk_inspection::capturing() && !super::rk_inspection::selected() { return None; }\n')
    note='crates/crypto/circuits/src/note.rs'
    source=read(runtime,note)
    old='    let rk = group::witness_subgroup(ctx, &w.rk, &w.rk.cofactor_preimage());\n    rk.assert_non_identity();'
    new='''    let rk = {
        #[cfg(feature = "formal-observer")]
        let _rk_scope = group::rk_inspection::scope();
        let rk = group::witness_subgroup(ctx, &w.rk, &w.rk.cofactor_preimage());
        rk.assert_non_identity();
        rk
    };'''
    generated['runtime/'+note]=replace_once(source,old,new)
    catalogue='crates/crypto/circuits/src/catalogue.rs'
    generated['runtime/'+catalogue]=read(runtime,catalogue)+'\ninclude!("catalogue/rk_inspection.rs");\n'
    for path in ('crates/crypto/circuits/src/group/rk_inspection.rs',
                 'crates/crypto/circuits/src/catalogue/rk_inspection.rs'):
        generated['runtime/'+path]=read(runtime,path)
    exporter='integration/src/bin/transfer-ownership-inspection.rs'
    source=read(formal,exporter)
    source=replace_once(source,'    let args: Vec<_> = std::env::args().skip(1).collect();\n',
        '    let args: Vec<_> = std::env::args().skip(1).collect();\n'
        '    if args.len() == 2 && args[0] == "rk-subgroup-spool" { return capture_rk_subgroup(&args[1]); }\n')
    source=replace_once(source,'        Some("shieldd-transfer-fixed-spend-v1") |',
        '        Some("shieldd-transfer-rk-subgroup-v1") |\n        Some("shieldd-transfer-fixed-spend-v1") |')
    generated['formal/'+exporter]=source+'\ninclude!("../inspection/transfer_rk_subgroup.rs");\n'
    include='integration/src/inspection/transfer_rk_subgroup.rs'
    generated['formal/'+include]=read(formal,include)
    for path,digest in originals.items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest:
            raise RelationError('RK source drift before packet publication')
    destination.mkdir(parents=True)
    for path,source in generated.items():
        target=destination/path; target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('x',encoding='utf8',newline='\n') as handle:handle.write(source)
    manifest=dict(scope='fresh source packet only; build/four-spool qualification/ingress/kernel/native joins open',
                  qualification=False,certification=False,originals=originals,
                  sources={path:hashlib.sha256(source.encode()).hexdigest() for path,source in generated.items()},
                  modes=['rk-subgroup-spool PREFIX','ordinary-spool PREFIX',
                         'qualify-spools FIRST ORDINARY1 ORDINARY2 REPEATED'],
                  staging='Overlay only into a fresh runtime/formal stage; preserve active source/binary inventories.')
    with (destination/'manifest.json').open('x',encoding='utf8') as handle:json.dump(manifest,handle,indent=2)
    return manifest


def prepare_merged(destination, t4_packet, controls_receipts, runtime_root, formal_root, *, clean_runtime_root=None):
    """Compose retained source65/map plus RK over the source06 recipe.

    This writes a fresh overlay packet and a deferred Bash staging recipe only.
    It never reads WSL, executes a build, edits an active stage, or qualifies a
    capture. Source06's complete SDK/compiler/application inventories remain
    mandatory when the root later applies the recipe to a fresh directory.
    """
    destination,t4,controls,runtime,formal=map(Path,(destination,t4_packet,controls_receipts,runtime_root,formal_root))
    if destination.exists():raise RelationError('merged RK stage destination must be fresh')
    pin='844389ee069e1fb2e576708842d0b389b4d9a44a';inputs={}
    def read(path):
        data=path.read_bytes();inputs[str(path)]=hashlib.sha256(data).hexdigest();return data
    def safe(relative):
        if not isinstance(relative,str) or '\\' in relative or relative.startswith('/') or any(p in ('','.','..') for p in relative.split('/')) or ':' in relative:
            raise RelationError('merged RK stage relative path')
        return relative
    parent=json.loads(read(t4/'manifest.json'))
    if parent.get('pin')!=pin or parent.get('qualification') is not False or parent.get('certification') is not False:
        raise RelationError('merged RK source65 pin/scope')
    files=parent.get('files');mapping=parent.get('overlay')
    if not isinstance(files,dict) or not isinstance(mapping,dict) or len(mapping)!=30:
        raise RelationError('merged RK source65 inventory shape')
    payloads={}
    for relative,digest in files.items():
        safe(relative);data=read(t4/relative)
        if hashlib.sha256(data).hexdigest()!=digest:raise RelationError('merged RK source65 payload identity')
        payloads[relative]=data
    for path,digest in parent.get('inputs',{}).items():
        if hashlib.sha256(read(Path(path))).hexdigest()!=digest:raise RelationError('merged RK source65 ancestor identity')
    overlay={safe(target):payloads[safe(payload)] for target,payload in mapping.items()}
    def inventory(filename,expected_count=None):
        records={}
        for line in read(controls/filename).decode().splitlines():
            match=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
            if not match or safe(match[2]) in records:raise RelationError('merged RK source06 inventory framing')
            records[match[2]]=match[1]
        if not records or expected_count is not None and len(records)!=expected_count:
            raise RelationError('merged RK source06 inventory count')
        return records
    sdk=inventory('sdk-source.txt',51);compiler=inventory('compiler-source.txt',20)
    app=inventory('app-source.txt');locks=inventory('runtime-inputs.txt');examples=inventory('formal-exporters.txt')
    clean=Path(clean_runtime_root) if clean_runtime_root is not None else formal.resolve().parent/'shieldd-pr160-844389ee'
    # Source06 retained the eight formal transfer exporters separately. The
    # clean pin also has two ordinary native examples; full directory admission
    # must retain them rather than narrowing the staging path check.
    clean_examples={}
    for basename in ('catalogue_shapes.rs','export_poseidon.rs'):
        relative='crates/crypto/circuits/examples/'+basename
        if relative in examples:raise RelationError('merged RK clean example inventory overlap')
        clean_examples[relative]=hashlib.sha256(read(clean/relative)).hexdigest()
    examples.update(clean_examples)
    for suffix in ('before','after'):
        if read(controls/('clean-head-'+suffix+'.txt')).decode().strip()!=pin or read(controls/('clean-status-'+suffix+'.txt')).strip():
            raise RelationError('merged RK source06 clean pin receipt')
    group='crates/crypto/circuits/src/group.rs';recorder='crates/crypto/circuits/src/group/inspection.rs'
    group_data=read(runtime/group)
    old_controls=json.loads(read(controls/'overlay.json'))
    if hashlib.sha256(group_data).hexdigest()!=old_controls.get('group_base_sha256'):
        raise RelationError('merged RK source06 group base')
    group_data+=b'\n#[cfg(test)]\n#[path = "group/formal_scalar_codec_tests.rs"]\nmod formal_scalar_codec_tests;\n'
    if hashlib.sha256(group_data).hexdigest()!=sdk.get(group) or sdk[group]!=old_controls.get('group_after_sha256'):
        raise RelationError('merged RK source06 codec test hook')
    recorder_data=read(runtime/recorder)
    if hashlib.sha256(recorder_data).hexdigest()!=sdk.get(recorder):raise RelationError('merged RK recorder source06 identity')
    sources={group:group_data,recorder:recorder_data,
             'crates/crypto/circuits/src/note.rs':overlay['crates/crypto/circuits/src/note.rs'],
             'crates/crypto/circuits/src/catalogue.rs':overlay['crates/crypto/circuits/src/catalogue.rs']}
    for relative in ('crates/crypto/circuits/src/group/rk_inspection.rs','crates/crypto/circuits/src/catalogue/rk_inspection.rs'):
        sources[relative]=read(runtime/relative)
    exporter='crates/crypto/circuits/examples/transfer-ownership-inspection.rs'
    include=read(formal/'integration/src/inspection/transfer_rk_subgroup.rs')
    # Reuse the existing exact hook implementation on minimal disposable source
    # roots. Every persistent input is already retained above by real identity.
    with tempfile.TemporaryDirectory() as temporary:
        temp=Path(temporary);vr=temp/'runtime';vf=temp/'formal'
        for relative,data in sources.items():
            target=vr/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        for relative,data in {'integration/src/bin/transfer-ownership-inspection.rs':overlay[exporter],
                              'integration/src/inspection/transfer_rk_subgroup.rs':include}.items():
            target=vf/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        composed=temp/'composed';prepare(composed,vr,vf)
        for relative in sources:overlay[relative]=(composed/'runtime'/relative).read_bytes()
        rendered=(composed/'formal/integration/src/bin/transfer-ownership-inspection.rs').read_bytes()
        anchor=b'include!("../inspection/transfer_rk_subgroup.rs");'
        if rendered.count(anchor)!=1:raise RelationError('merged RK exporter include shape')
        overlay[exporter]=rendered.replace(anchor,b'include!("../src/transfer_rk_subgroup_export.rs");')
        overlay['crates/crypto/circuits/src/transfer_rk_subgroup_export.rs']=include
    old_exporter=payloads[mapping[exporter]].decode();new_exporter=overlay[exporter].decode()
    functions=re.findall(r'^fn ([A-Za-z_][A-Za-z0-9_]*)\(',old_exporter,re.M)
    if len(functions)!=len(set(functions)) or any(new_exporter.count('fn '+name+'(')!=1 for name in functions):
        raise RelationError('merged RK exporter function preservation')
    for mode in ('ordinary-spool','fixed-spend-spool','roles-spool','qualify-spools','transfer-t4-pages-spool'):
        if new_exporter.count('"'+mode+'"')!=old_exporter.count('"'+mode+'"'):
            raise RelationError('merged RK existing exporter mode changed')
    for path,digest in inputs.items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest()!=digest:raise RelationError('merged RK publication source drift')
    destination.mkdir(parents=True)
    result={relative:'overlay/'+relative for relative in sorted(overlay)}
    for relative,data in overlay.items():
        target=destination/result[relative];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    manifest=dict(pin=pin,scope='fresh source06/65/map/RK overlay recipe only; build/capture/ordinary2/repeat/native/kernel joins open',
                  qualification=False,certification=False,inputs=inputs,source65_manifest_sha256=inputs[str(t4/'manifest.json')],
                  source06_inventory=dict(sdk=sdk,compiler=compiler,app=app,locks=locks,exporters=examples),
                  clean_pin_examples=clean_examples,
                  activation_base_files=parent['activation_base_files'],overlay=result,
                  files={payload:hashlib.sha256(overlay[relative]).hexdigest() for relative,payload in result.items()},
                  exporter_functions=functions+['capture_rk_subgroup'],
                  modes=['ordinary-spool','fixed-spend-spool','roles-spool','qualify-spools','transfer-t4-pages-spool','rk-subgroup-spool'])
    recipe='''#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
# Root-owned deferred activation only. This script does not build or capture.
[[ $# == 4 ]] || { echo 'usage: stage.sh SOURCE06 FRESH_DEST PACKET CLEAN_PIN' >&2; exit 2; }
source06=$(realpath -e -- "$1")
packet=$(realpath -e -- "$3")
clean_pin=$(realpath -e -- "$4")
[[ ! -e "$2" ]] || { echo 'destination must be fresh' >&2; exit 2; }
destination=$(realpath -m -- "$2")
[[ "$destination" = /* && "$destination" != / && "$destination" != "$source06" && "$destination" != "$source06/"* && "$source06" != "$destination/"* ]] || exit 2
[[ $(git -C "$clean_pin" rev-parse HEAD) == 844389ee069e1fb2e576708842d0b389b4d9a44a ]] || exit 2
[[ -z $(git -C "$clean_pin" status --porcelain) ]] || exit 2
verify_base() {
  (cd "$source06"; sha256sum --quiet -c "$packet/base-inventory.sha256")
  (cd "$source06"; find crates/crypto/circuits/src -type f -name '*.rs' | sort) | cmp - "$packet/sdk-paths.txt"
  (cd "$source06"; find third_party/commonware/cryptography/src/zk -type f -name '*.rs' | sort) | cmp - "$packet/compiler-paths.txt"
  (cd "$source06"; find crates/core/app/src -type f -name '*.rs' | sort) | cmp - "$packet/app-paths.txt"
  (cd "$source06"; find crates/crypto/circuits/examples -type f -name '*.rs' | sort) | cmp - "$packet/exporter-paths.txt"
}
verify_base
(cd "$packet"; sha256sum --quiet -c payload-inventory.sha256)
mkdir -- "$destination"
(cd "$source06"; tar --exclude='.git' -cf - .) | (cd "$destination"; tar -xf -)
while IFS=$'\\t' read -r relative payload; do
  mkdir -p -- "$destination/$(dirname -- "$relative")"
  cp -- "$packet/$payload" "$destination/$relative"
done < "$packet/overlay.tsv"
(cd "$destination"; sha256sum --quiet -c "$packet/staged-overlay.sha256")
verify_base
[[ -z $(git -C "$clean_pin" status --porcelain) ]] || exit 2
echo 'Source-only fresh overlay staged; no build, capture or qualification performed.'
'''
    receipt_files={
        'stage.sh':recipe,
        'overlay.tsv':''.join(relative+'\t'+payload+'\n' for relative,payload in result.items()),
        'base-inventory.sha256':''.join(digest+'  '+relative+'\n' for relative,digest in sorted({**sdk,**compiler,**app,**locks,**examples}.items())),
        'staged-overlay.sha256':''.join(hashlib.sha256(overlay[relative]).hexdigest()+'  '+relative+'\n' for relative in sorted(overlay)),
        'sdk-paths.txt':'\n'.join(sorted(sdk))+'\n',
        'compiler-paths.txt':'\n'.join(sorted(compiler))+'\n',
        'app-paths.txt':'\n'.join(sorted(app))+'\n',
        'exporter-paths.txt':'\n'.join(sorted(examples))+'\n',
        'payload-inventory.sha256':''.join(digest+'  '+relative+'\n' for relative,digest in sorted(manifest['files'].items()))}
    for relative,source in receipt_files.items():
        (destination/relative).write_bytes(source.encode('utf8'))
    manifest['recipe_files']={relative:hashlib.sha256(source.encode('utf8')).hexdigest() for relative,source in receipt_files.items()}
    (destination/'manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf8')
    return manifest
