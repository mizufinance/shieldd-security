"""Publish scoped whole-call checkpoint preserving producer/attribution identities."""
import hashlib,json,shutil
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];REPO=ROOT/'work/shared-build-handoff';BASE=REPO/'handoffs/transfer-20261009';O=ROOT/'outputs/mac-poseidon-width3-call10'
DEST=BASE/'sources/mac/poseidon-width3-call10';REV=BASE/'reviews/poseidon-width3-call10';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((O/'publication-manifest01.json').read_text());env=json.loads((O/'publication-envelope01.json').read_text());a=json.loads((H/'seal-audit01.json').read_text())
assert sha(O/'publication-manifest01.json')==env['producer_manifest']['sha256']==a['manifest_sha256']
assert sha(O/'publication-envelope01.json')=='cac4a140ad92ceff160fffc2d389532a517da573a0c19fe5f5d494fb32230967'
assert a['main_fresh_modules']==22 and a['main_exact_declaration_audits']==178
assert not DEST.exists() and not REV.exists();DEST.mkdir(parents=True);REV.mkdir(parents=True)
handwritten=[];generated=[];omitted=[];seen=set();canonical_modules=0
for x in m['files']+env['postseal_entries']:
    if x['path'] in seen:continue
    seen.add(x['path']);src=ROOT/x['path'];assert sha(src)==x['sha256'] and src.stat().st_size==x['bytes']
    if not x['publication']:
        omitted.append(dict(x,parent_disposition='Retained locally, zero extra credit'));continue
    dst=DEST/x['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
    kind=x['category'];paths=handwritten if kind in {'maintained_generator_or_guard','maintained_template','handwritten_or_canonical_helper','postseal_transport_generator'} else generated
    paths.append(str(dst.relative_to(REPO)))
    if '/mac-poseidon-width3-call10/project/ShielddSecurity/' in x['path'] and src.stem in m['receipts']:
        canonical=REPO/'circuits/ShielddSecurity'/src.name
        chosen=ROOT/m['attribution_successor']['source'] if src.stem=='TransferPoseidonWidth3Prefix10AbsorbProof01' else src
        if canonical.exists():assert sha(canonical)==sha(chosen)
        else:shutil.copyfile(chosen,canonical);paths.append(str(canonical.relative_to(REPO)));canonical_modules+=1
for src in [O/'publication-manifest01.json',O/'publication-envelope01.json']:
    dst=DEST/src.relative_to(ROOT);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);generated.append(str(dst.relative_to(REPO)))
for name in ['parent-width3-call10-review01','parent-width3-call10-review02']:
    origin=ROOT/'work'/name;dst=REV/name;dst.mkdir()
    reviewfile=origin/('prefix-opus55-review01.json' if name.endswith('01') else 'opus55-review.json');j=json.loads(reviewfile.read_text());assert not j['is_error'] and 'claude-opus-5-5' in j['modelUsage']
    for p in origin.iterdir():
        if p.is_file() and p.suffix in {'.json','.py'}:
            shutil.copyfile(p,dst/p.name);generated.append(str((dst/p.name).relative_to(REPO)))
dst=DEST/'README.md';dst.write_text('''# Domain-18 one-input width3 whole call

The arbitrary-assignment endpoint proves the independent mathematical hash3 with domain18, arity1, IV274, zero padding and output state1. Both prefix rounds0/1 and suffix rounds2..64 use the same final assignment. The total constructor runs238steps (237 materialized and one copy), satisfies317selected rows38876..39191 plus copy200769, preserves all22735original inputs at3+input and all columns outside writes61614..61929, copy and the six-term input LC cut363983. It conditionally preserves476earlier local page rows38400..38875 if the base satisfies them. Exact positional rowAt equality ties every selected row to its capture index in page38400..39423 plus copy. This local page has1025rows; later232rows39192..39423 are not claimed satisfied or preserved.

Main22fresh modules passed178complete type/axiom audits, including one cost-only True marker. The21proof-root modules account for177audits. A separately regenerated attribution-only successor has10fresh audits and the identical proof object; it adds no mathematical result. The canonical AbsorbProof source uses that corrected generator header. Original successful source and import receipt identities remain unchanged in the producer packet.

Parent checks rehashed148producer and5postseal records,134inherited source/object/receipt identities and134canonical source identities, reparsed existing successful type/axiom logs, independently checked44raw nodes26constants17prefixrows/fourcuts and the suffix boundary against the pinned DB/parameters. Portable byte regeneration passed19generated sources:18match original accepted bytes,one matches the separately audited header successor. Two actual Claude Opus5.5 high source reviews found no mathematical defect or actionable whole-call/page defect. The parent omission of the probe generator was resolved by the second review. Nine absorption/round and five page-selection rejection checks are finite Bool guard statements; the positive page check also passes. They do not establish semantic inequalities or exhaustive corruption detection. Five failed kernel predecessors retain zero credit.

Use verify_replay.py with explicit descriptor rounds02.json, tail-reference01.json, exact pinned poseidon381.json, generation-replay-input01.json, canonical inherited source directory and a fresh workspace. Only source bytes are regenerated. The recipe reads its maintained inputs beside itself and checks all hashes. There is no Lean replay or raw capture replay in this recipe. Maintained sources and templates are shipped under work/mac-poseidon-width3-call10; qualified inputs are under outputs/mac-poseidon-width3-call10. Raw observations, caches, objects and composed workspaces remain local and their immutable identities are retained.

Field/CharP fixedp, rho/base0=1,4≠0 and copy-link hypotheses are explicit; prior satisfaction is required only for the476row frame. The priorRows range follows by definition, with no separately named range theorem. Upstream cut evaluation, native callsite/raw consumer identity (including365617), global200770row frame/partition, all210calls, clean verifier/VK correspondence and full Transfer remain OPEN. Limits remain LEAN_NUM_THREADS=1,-j1,-M2048,240seconds/module,4GiBgroupRSS,15percent free memory and2GiB free disk. No parent kernel run or final certification refresh occurred.
''');generated.append(str(dst.relative_to(REPO)))
public={str(p.relative_to(DEST)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(DEST.rglob('*')) if p.is_file()}
dst=DEST/'publication-manifest.json';dst.write_text(json.dumps({'schema':'parent-reviewed-local-whole-call-page-publication-v1','files':public,'omitted_local':omitted,'producer_manifest_sha256':sha(O/'publication-manifest01.json'),'postseal_envelope_sha256':sha(O/'publication-envelope01.json'),'main_fresh_modules':22,'main_declaration_audits':178,'attribution_successor_audits':10,'attribution_new_math_credit':0,'generated_sources_reproduced':19,'canonical_new_modules':canonical_modules,'parent_kernel_runs':0,'full_transfer':'OPEN'},indent=2)+'\n');generated.append(str(dst.relative_to(REPO)))
dst=BASE/'receipts/mac/poseidon-width3-call10.json';dst.write_text(json.dumps({'schema':'reviewed-local-whole-call-page-publication-envelope-v1','producer_scope':json.loads((O/'scope01.json').read_text()),'publication_manifest_sha256':sha(DEST/'publication-manifest.json'),'review_path':str(REV.relative_to(BASE)),'full_transfer':'OPEN'},indent=2)+'\n');generated.append(str(dst.relative_to(REPO)))
assert len(set(handwritten+generated))==len(handwritten)+len(generated)
(H/'publication-staging01.json').write_text(json.dumps({'handwritten':handwritten,'generated_evidence':generated,'canonical_modules':canonical_modules,'packet_files':len(public),'omitted_local_files':len(omitted)},indent=2)+'\n');print(json.dumps({'canonical_modules':canonical_modules,'packet_files':len(public),'omitted_local_files':len(omitted)}))
