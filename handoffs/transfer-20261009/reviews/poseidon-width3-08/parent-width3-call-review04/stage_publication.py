"""Publish reviewed width3 sources and sealed scoped evidence; no Lean run."""
import hashlib,json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT/'work/shared-build-handoff'
BASE=REPO/'handoffs/transfer-20261009'
DEST=BASE/'sources/mac/poseidon-width3-08'
REV=BASE/'reviews/poseidon-width3-08'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
producer=ROOT/'outputs/mac-poseidon-width3-08/publication-manifest02.json'
successor=ROOT/'work/mac-poseidon-width3-08/transport-successor01/manifest01.json'
envelope=successor.with_name('envelope01.json')
m=json.loads(producer.read_text());s=json.loads(successor.read_text());e=json.loads(envelope.read_text())
assert sha(producer)==e['producer_manifest_sha256'] and sha(successor)==e['successor_manifest_sha256']
for item in m['files']+s['files']:assert sha(ROOT/item['path'])==item['sha256'],item['path']
for item in m['inherited_imports'].values():
    p=REPO/'circuits'/Path(item['source_path']).relative_to('work/mac-poseidon-width3-08/project')
    assert sha(p)==item['source_sha256']
audit=json.loads((ROOT/'work/parent-width3-call-review03/receipt-audit02.json').read_text())
assert audit['modules']==81 and audit['audits']==1998 and audit['full_types']==1998
assert all(x['unchanged'] for x in audit['frozen_source_matches'])
assert not DEST.exists() and not REV.exists(),'fresh publication destination required'
DEST.mkdir(parents=True);REV.mkdir(parents=True)
overrides={x['path']:x for x in s['classification_overrides']}
handwritten=[];generated=[];omitted=[]
for item in m['files']+s['files']:
    x=dict(item);x.update(overrides.get(item['path'],{}))
    if not x['publication']:
        omitted.append(x);continue
    src=ROOT/x['path'];target=DEST/x['path'];target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
    relative=str(target.relative_to(REPO))
    if x['category'] in {'handwritten_generator_or_guard','maintained_proof_or_control_template','handwritten_helper_or_verification_floor'} or src.name in {'verify_replay_portable.py','run_portable.py','seal_successor.py'}:handwritten.append(relative)
    else:generated.append(relative)
    if '/project/ShielddSecurity/' in x['path'] and src.stem in m['current_pass_receipts']:
        canonical=REPO/'circuits/ShielddSecurity'/src.name
        assert not canonical.exists()
        shutil.copyfile(src,canonical)
        (generated if x['category']=='generated_instance' else handwritten).append(str(canonical.relative_to(REPO)))
for src in [producer,ROOT/'outputs/mac-poseidon-width3-08/publication-envelope01.json',successor,envelope]:
    target=DEST/src.relative_to(ROOT);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target);generated.append(str(target.relative_to(REPO)))
review_dirs=['parent-width3-review01','parent-width3-review02','parent-width3-call-review03','parent-width3-call-review04']
for name in review_dirs:
    origin=ROOT/'work'/name;destination=REV/name;destination.mkdir()
    review=json.loads((origin/'opus55-review.json').read_text());assert not review['is_error'] and 'claude-opus-5-5' in review['modelUsage']
    for p in sorted(origin.iterdir()):
        if not p.is_file() or p.suffix not in {'.json','.py'}:continue
        if p.name.startswith('receipt-audit') and p.name!='receipt-audit02.json':continue
        shutil.copyfile(p,destination/p.name);generated.append(str((destination/p.name).relative_to(REPO)))
readme=DEST/'README.md'
readme.write_text('# Scoped width3 Poseidon call\n\nThe first captured domain24/arity2 width3 call has 65-round arbitrary-assignment soundness and a constructor for all321 selected rows, preserving all22735 inputs, original columns, copy and actual cut LCs. The independent hash3 output is internal state1. Inputs16577/21951 remain prior LC cuts. The worker passed81 fresh modules and1998 exact full-type/standard-axiom audits; the parent re-parsed the existing successful logs and rehashed374 producer/successor records and20 inherited canonical sources. Four Claude Opus5.5 source reviews found no mathematical defect within their scopes. No parent kernel rerun occurred.\n\nThe portable recipe reproduced78 generated sources byte-for-byte using nine supported generators. Invoke work/mac-poseidon-width3-08/transport-successor01/verify_replay_portable.py with explicit --manifest, --envelope, --source-dir, --small-descriptor, --descriptor, --parameter and fresh --output arguments. The manifest/envelope are outputs/mac-poseidon-width3-08/publication-manifest02.json and publication-envelope01.json; source-dir is work/mac-poseidon-width3-08. The two large finite descriptors and exact pinned parameter bytes must be supplied separately; their hashes are checked. This replays source generation only. Raw capture requalification and kernel replay are separate operations. The historical bootstrap is omitted and never required. Source paths inside producer records identify original local inputs; publication-manifest.json identifies shipped paths.\n\nArithmetic and absorption controls retain their precise production-check scopes. Traversal/output controls prove guard rejection, not output inequality. The import-floor True marker measures import cost only. Failed compiler, preflight, seal and byte-replay attempts retain zero credit. Preserved predecessors/checkpoints are historical observations.\n\nRaw logs, descriptors, proof objects and caches stay local. Actual full parent-row inclusion/global frame, upstream input semantics, raw consumer association, all210 call joins, native correspondence and full Transfer remain OPEN. No final certification or atomic certification refresh occurred. NEXT_TASK.md is a proposal; the new parent assigned its bounded second-tail/page scope separately.\n')
generated.append(str(readme.relative_to(REPO)))
public={str(p.relative_to(DEST)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(DEST.rglob('*')) if p.is_file()}
manifest={'schema':'parent-scoped-width3-publication-v1','files':public,'omitted_local':omitted,'producer_manifest_sha256':sha(producer),'successor_manifest_sha256':sha(successor),'successor_envelope_sha256':sha(envelope),'modules':81,'type_axiom_audits':1998,'generated_sources':78,'parent_kernel_runs':0,'full_transfer':'OPEN'}
p=DEST/'publication-manifest.json';p.write_text(json.dumps(manifest,indent=2)+'\n');generated.append(str(p.relative_to(REPO)))
receipt={'schema':'reviewed-width3-publication-envelope-v1','publication_manifest_sha256':sha(p),'producer_manifest_sha256':sha(producer),'successor_envelope_sha256':sha(envelope),'review_path':str(REV.relative_to(BASE)),'module_count':81,'full_type_axiom_audits':1998,'generated_byte_replay':78,'kernel_rerun':False,'scope':'domain24/arity2 mathematical hash3 of captured cut LCs; full parent inclusion/upstream/native OPEN','full_transfer':'OPEN'}
p=BASE/'receipts/mac/poseidon-width3-08.json';p.write_text(json.dumps(receipt,indent=2)+'\n');generated.append(str(p.relative_to(REPO)))
(HERE/'publication-staging01.json').write_text(json.dumps({'handwritten':handwritten,'generated_and_evidence':generated,'files':len(public),'omitted':len(omitted),'canonical_modules':81,'full_transfer':'OPEN'},indent=2)+'\n')
print(json.dumps({'public_files':len(public),'canonical_modules':81,'handwritten_paths':len(handwritten),'generated_evidence_paths':len(generated),'full_transfer':'OPEN'}))
