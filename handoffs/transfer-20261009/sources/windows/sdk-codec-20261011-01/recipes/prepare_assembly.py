"""Portable incremental codec packet gated on all33 complete accepted audits."""
import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-sdk-admission-endpoint-20261010-01/assemble.py'
text = prior.read_text().split('rejected = []\n')[0]
text = text.replace('Seal18scoped sources/92audits', 'Seal4scoped sources/33audits')
start = text.index('STAGES = ['); end = text.index('\n\ndef pin',start)
text = text[:start]+"STAGES = [('transfer-sdk-byte-iterator-model-20261010-02', 1),\n          ('transfer-sdk-decoder-model-20261010-02', 1),\n          ('transfer-sdk-sign-selection-model-20261010-02', 1),\n          ('transfer-sdk-codec-join-20261010-01', 1)]"+text[end:]
text = text.replace('len(entries) == 7','len(entries) == 4').replace('== 7\n','== 4\n')
text = text.replace("== 98\n","== 33\n")
text = text.replace("e['module'] in ['SDKSpendAuthCertificates01']","e['module'] in []")
text += r'''
rejected = []
for task_name, module, classification in [
    ('transfer-sdk-byte-iterator-model-20261010-01','SDKByteIterator01','Final take-width simplification: compiler rejection'),
    ('transfer-sdk-decoder-model-20261010-01','SDKCompressedDecoder01','Linear-combination sign, constructor equality and product association: compiler rejection'),
    ('transfer-sdk-sign-selection-model-20261010-01','SDKSignSelection01','Coordinate projection transport mismatch: compiler rejection')]:
    task = DIAG / task_name
    records = [pin(task / name) for name in ['plan.json','review.json','events.jsonl','execute_bounded.py','handwritten/'+module+'.lean','runs/01-'+module+'/stdout.txt']]
    assert json.loads((task/'events.jsonl').read_text().splitlines()[-1])['result']['status'] == 'failed'
    rejected.append({'task':task_name,'classification':classification,'immutable_records':records,'rejected_attempt_credit':0,'semantic_negative_control_credit':0})
(packet / 'receipts').mkdir()
(packet / 'receipts/rejected-attempts.json').write_text(json.dumps(rejected,indent=2)+'\n')
(packet / 'receipts/qualified-phases.json').write_text(json.dumps(phases,indent=2)+'\n')
floor = DIAG/'transfer-sdk-codec-owned-floor-20261010-01'
for name in ['prepare.py','prepare_recipe.py','composition-review.json']:
    copy(floor/name,'owned-import-context/'+name)
for task_name,module in [('transfer-sdk-byte-iterator-model-20261010-02','SDKByteIterator01'),('transfer-sdk-decoder-model-20261010-02','SDKCompressedDecoder01'),('transfer-sdk-sign-selection-model-20261010-02','SDKSignSelection01')]:
    copy(DIAG/task_name/'prepare_fresh.py','recipes/'+module+'-repair.py')
copy(DIAG/'transfer-sdk-codec-recipes-20261010-01/prepare_recipes.py','recipes/prepare-successor-recipes.py')
check = DIAG/'transfer-sdk-codec-checkpoint-20261010-02'
for name in ['preservation.json','preservation_check.py','prepare.py']:
    copy(check/name,'receipts/'+name)
parent = DIAG/'transfer-sdk-admission-endpoint-20261010-01'
copy(parent/'packet/manifest.json','inputs/sdk-admission-parent-manifest.json')
source = DIAG/'transfer-sdk-source-binding-20261010-01'
copy(source/'source-identities.json','source-provenance/source-identities.json')
copy(source/'sources/jubjub-0.10.0/src/lib.rs','source-provenance/pinned-sdk/jubjub-0.10.0/src/lib.rs')
copy(Path(__file__),'recipes/assemble.py')
copy(ROOT/'prepare_assembly.py','recipes/prepare_assembly.py')
runner_checks = []
for task_name,_ in STAGES:
    runner = pin(DIAG/task_name/'execute_bounded.py')
    assert runner['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
    runner_checks.append(runner)
(packet/'receipts/unchanged-runners.json').write_text(json.dumps({'runners':runner_checks,'physical_guard_changes':False,'runtime_credit':0},indent=2)+'\n')
files=[]
for path in sorted(packet.rglob('*')):
    if path.is_file():
        record=pin(path); record['path']=path.relative_to(packet).as_posix(); files.append(record)
manifest={'kind':'SCOPED_MATHEMATICAL_SDK_ITERATOR_DECODER_AND_CONCRETE_JOIN',
    'files':files,'source_files':4,'handwritten_sources':4,'generated_sources':0,'type_axiom_pairs':33,
    'modules':[{'module':e['module'],'source_sha256':e['source']['sha256'],'audit_pairs':len(e['audits']),'source_class':e['source_class']} for e in entries],
    'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a',
    'sdk_admission_parent_archive':pin(parent/'portable-windows-sdk-admission-endpoint01.tar.xz'),
    'latest_parent_canonical_sha_at_seal':'6b85891f959e9aeb475945f26092f5ae7849fc5a',
    'scope':'Exact mathematical reverse-byte/reverse-inner-bit/skip-four iterator equals the reversed252-bit reader by a symbolic range-block recurrence. Generic decoder denominator is nonzero; fixed-y square roots differ only by sign; canonical sign parity determines the certified SDK base. Source root selection and ZIP216 guard derive that decoded result without an assumed point identity or nonzero-root premise. Concrete source loop gives scalar multiplication, literal modulus-byte subgroup test, and decoded SDK-base subgroup membership.',
    'guard_delta':'No physical or packaging guard changes. Four runner bodies byte-identical to accepted baseline. Lean heap1536MiB/j1/finite300000 heartbeats/rec4096/240s per module/600s per task/4GiB Job/free-memory/commit/disk-pressure/mutex retained.',
    'open_obligations':['Actual Rust iterator/field/canonical-byte/strict decoder/sqrt/sign representation correspondence','Whole Transfer row/copy/native correspondence and final portable replay'],
    'runtime_test_credit':0,'bounded_model_check_credit':0,'semantic_negative_control_credit':0,'native_source_correspondence_credit':0,
    'full_transfer':'OPEN','certification':False,
    'repository_payload_policy':'Handwritten sources, normalized complete type/axiom reports, immutable plan/runner/provenance and reviewed SDK snapshot. No raw compiler logs, objects, toolchains, caches or composed runtime workspaces.'}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
archive=ROOT/'portable-windows-sdk-codec-endpoint01.tar.xz'
with tarfile.open(archive,'w:xz',preset=6) as tar:
    for path in sorted(packet.rglob('*')):
        if path.is_file():
            data=path.read_bytes(); info=tarfile.TarInfo(path.relative_to(packet).as_posix()); info.size=len(data); info.mtime=0; info.mode=0o644
            tar.addfile(info,io.BytesIO(data))
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 128*1024**2
print(json.dumps({'archive':pin(archive),'manifest':pin(packet/'manifest.json'),'sources':4,'audits':33,'full_transfer':'OPEN','certification':False}))
'''
# Preserve actual JSON newline bytes rather than literal backslash-n sequences.
text = text.replace("+'\\\\n'", "+'\\n'")
ast.parse(text)
(ROOT/'assemble.py').write_text(text,encoding='utf-8',newline='\n')
print('Four sources,33 audits assembly prepared; qualified passes required before sealing.')
