"""Seal a retained-runtime review packet; never promote a formal gate."""
import hashlib, io, json, tarfile
from pathlib import Path
OUT=Path(__file__).resolve().parent
DIAG=OUT.parent
D=DIAG/'transfer-implementation-20261002'
REVIEW=DIAG/'transfer-runtime-receipt-review-20261010-01'
CAPTURE=DIAG/'transfer-runtime-overlay-review-20261010-01'
def pin(p):
    return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
r=json.loads((REVIEW/'review.json').read_bytes())
c=json.loads((CAPTURE/'capture.json').read_bytes())
assert r['exact_named_tests']==23 and r['genuine_branches']==17
assert c['source_matches_retained_inventory'] and all(b['current_matches_receipt'] for b in c['binaries'].values())
assert len(c['differences'])==52
source_review=dict(kind='DIAGNOSTIC_OVERLAY_SOURCE_BOUNDARY_REVIEW',
    runtime_sha=r['runtime_sha'],clean_runtime_status='UNCHANGED_CLEAN_FULL_SHA',
    captured_source_files=c['source_files'],different_paths=52,
    findings=[
        'Transaction execution and delivery retain the production paths and add only cfg(test), transaction-ID-bound fault branches after routing and after indexing.',
        'Host, service and registry wrappers add test includes; the host queue fixture directly injects canonical no-action entries and cannot establish genuine Transfer retry safety.',
        'Circuit modules contain feature-gated observers plus unconditional handle-preserving expression refactors. Clone semantics and full ordered original-row correspondence remain separate obligations; raw hashes do not discharge them.',
        'Commonware adds diagnostic methods; the existing ordinary compiler entry point is unchanged in the captured diff. Added methods still require their own replay correspondence if used for G3/G4.',
        'Cargo.lock adds commonware-math as an already locked development dependency of proof-params; the diagnostic overlay and its dependency list differ from the clean runtime snapshot.',
        'Twenty-three named tests and seventeen branch examples actually passed in the retained runs. Their captured identities, current live source inventory and six current executable hashes agree.',
        'The six permanent-store tests test all partition-prefix commit counts in their finite fixtures and an application-selected recovery boundary including empty genesis; they do not cover all completion errors after durable writer commit.'
    ],formal_refinement=False,full_transfer_certification=False)
status=dict(kind='TRANSFER_COMPLETION_MILESTONE_SUCCESSOR',
    supersedes_unreviewed_successor_section_only=pin(DIAG/'transfer-completion-status-20261010-01/status.json'),
    runtime_sha=r['runtime_sha'],envelope_join=dict(sources=3,audits=35,status='SCOPED_KERNEL_PASS',
        archive_sha256='a358dda6ad9af9f5b9c6d27453ac0d9e62610160aa2d8db9b996fee72cd6049a',
        complete_transport_parts=24),
    retained_runtime=dict(named_tests=23,genuine_branch_examples=17,source_files=1239,
        binary_identity_matches=6,source_overlay_differences=52,new_executions=0,
        receipt_review=pin(REVIEW/'review.json'),live_identity_capture=pin(CAPTURE/'capture.json')),
    remaining_dependencies=[
        'Retained3130 remains partial after DH role4 phase08; phases09..14 and the subsequent24 controller stages have no completed receipts in that chain. Do not resume wide unrolled constraints without a symbolic source review.',
        'The fresh full native suite remains unlaunched. The independently completed coherent23 tests/17 branch examples cover their exact names and fixtures, not every test in every old plan.',
        'Delayed Ordinary-token volume interleaving is unrun in the old delayed04 plan, which requires obsolete Registry05. Prepare a fresh reviewed source09/Registry06 successor retaining the exact semantic failure assertions and physical guards.',
        'Original full-row/source/algorithm G3/G4 uses the Mac provider when ready. Generic model joins and diagnostic hash matches are prerequisites, not complete implementation correspondence.',
        'Rust extraction, finite containers, byte codec, key and cryptographic primitive contracts and production Host writer durability need owned correspondence and honest failure consequences.',
        'Atomic certification requires all claim obligations and the clean exact shieldd.lock SHA; no certification is granted by this milestone.'
    ],new_proof_credit=0,new_runtime_executions=0,certification=False)
entries={}
def add(p,name):
    assert name not in entries
    entries[name]=(p,pin(p))
for folder,label in [(REVIEW,'receipt-review'),(CAPTURE,'overlay-review')]:
    for p in folder.rglob('*'):
        if p.is_file(): add(p,label+'/'+p.relative_to(folder).as_posix())
for job in r['jobs']:
    folder=D/job['output']
    for record in job['receipts']+job['paired_receipts']:
        p=Path(record['path'])
        assert pin(p)==record
        name='retained-receipts/'+job['output']+'/'+p.name
        if name not in entries: add(p,name)
    for name in ['build-receipt.json','alternate-registry-published.json','binary-before.json',
        'runtime-completed.json','group-result.json','libtest-results.txt','source-stage-validated.json',
        'cgroup-limits.txt','preflight-memory.txt','task-swap-cleanup.txt']:
        p=folder/name
        key='retained-receipts/'+job['output']+'/'+name
        if p.is_file() and key not in entries:add(p,key)
for packet_name in ['transfer-coherent-controls-execution-22','transfer-coherent-controls-execution-23']:
    folder=D/packet_name
    for p in folder.iterdir():
        if p.is_file():add(p,'retained-execution-source/'+packet_name+'/'+p.name)
for name in ['source-boundary-review.json','completion-status02.json']:
    p=OUT/name
    assert not p.exists()
    value=source_review if name.startswith('source-') else status
    p.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
    add(p,name)
add(Path(__file__),'assembly-recipe.py')
manifest=dict(kind='RETAINED_RUNTIME_REVIEW_PORTABLE_PACKET',runtime_sha=r['runtime_sha'],
    native_tests=23,genuine_branch_examples=17,new_replays=0,proof_credit=0,certification=False,
    boundaries=source_review,files={name:record for name,(p,record) in entries.items()})
manifest_raw=(json.dumps(manifest,indent=2)+'\n').encode()
manifest_path=OUT/'manifest.json'
assert not manifest_path.exists()
manifest_path.write_bytes(manifest_raw)
archive_path=OUT/'portable-windows-runtime-completion-review01.tar.xz'
assert not archive_path.exists()
with tarfile.open(archive_path,'w:xz',preset=6) as archive:
    for name,(p,record) in sorted(entries.items()):
        assert pin(p)==record
        info=tarfile.TarInfo(name);info.size=p.stat().st_size;info.mode=0o644
        with p.open('rb') as stream:archive.addfile(info,stream)
    info=tarfile.TarInfo('manifest.json');info.size=len(manifest_raw);info.mode=0o644
    archive.addfile(info,io.BytesIO(manifest_raw))
print(json.dumps(dict(archive=pin(archive_path),manifest=pin(manifest_path),status=pin(OUT/'completion-status02.json'),files=len(entries))))
