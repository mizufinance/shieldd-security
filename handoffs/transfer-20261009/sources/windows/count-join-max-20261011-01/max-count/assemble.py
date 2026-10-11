"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-ordinary-max-count-20261011-02'
CHECKPOINT = DIAG / 'transfer-ordinary-max-count-checkpoint-20261011-02'
MODULE = 'TransferOrdinaryMaxCount01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-ordinary-max-count-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 6 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 24 and len(pool['inherited_public_reports']) == 277
manager_endpoint = DIAG / 'transfer-ordinary-count-codec-join-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-ordinary-count-codec-join-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == 'ab52eb1fa05ea6581155298fe2eea78d67fd3e008debd2224dc1d9d50a79cf27'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 6 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferOrdinaryCountCodecJoin01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 277 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 24
for selected in pool['selected']:
    original = next(r for r in manager_selected if r['module'] == selected['module'])
    assert selected['source'] == original['source'] and selected['object'] == original['object']
    for k in ['source', 'object', 'copy']:
        assert pin(selected[k]['path']) == selected[k]
    carriers = [pin(manager_archive)]
    def collect_archive_refs(value):
        if isinstance(value, dict):
            if 'archive' in value and isinstance(value['archive'], dict) and 'path' in value['archive']:
                carriers.append(value['archive'])
            for nested in value.values():
                collect_archive_refs(nested)
        elif isinstance(value, list):
            for nested in value:
                collect_archive_refs(nested)
    collect_archive_refs(manager_reference)
    member = 'source/ShielddSecurity/' + selected['module'] + '.lean'
    found = False
    for carrier in {r['path']: r for r in carriers}.values():
        assert pin(carrier['path']) == carrier
        with tarfile.open(carrier['path'], 'r:xz') as tar:
            if member in tar.getnames():
                assert tar.extractfile(member).read() == Path(selected['source']['path']).read_bytes()
                found = True
                break
    assert found, selected['module']
def core_floor_refs(value):
    if isinstance(value, dict):
        if 'core_floor' in value:
            yield value['core_floor']['original']
        for nested in value.values():
            yield from core_floor_refs(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from core_floor_refs(nested)
assert plan['external_floor'] in list(core_floor_refs(manager_reference))
reference = {'concrete_codec_join': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 6},
    'ancestors': manager_reference, 'complete_owned_modules': 24, 'inherited_complete_reports': 277,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact twenty-four-module closure through typed-byte/concrete-codec whole Ordinary refusal, with all 277 inherited complete reports. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('generated/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'one exact maximal-u64 byte definition and five symbolic decoding/overflow/whole-delivery proofs; generated byte-exact')
add(stdout, 'reports/fresh-6-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete twenty-four-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 277 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(CURRENT / 'generate.py', 'qualified/generate.py', 'maintained generator; no generated source hand edits')
add(ROOT / 'regeneration.json', 'reports/regeneration.json', 'independent exact generated byte reproduction; zero proof credit')
add(DIAG / 'transfer-ordinary-max-count-endpoint-20261011-01/prepare_assembly_derived.py', 'predecessor-prepare_assembly_derived.py', 'original unexecuted sealer derivation; no proof credit')
REJECTED = DIAG / 'transfer-ordinary-max-count-20261011-01'
history = [json.loads(x) for x in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(history) == 2 and history[-1]['result']['status'] == 'failed'
import re
old = (REJECTED / ('generated/' + MODULE + '.lean')).read_text()
new = (CURRENT / ('generated/' + MODULE + '.lean')).read_text()
def signatures(text):
    return [text[match.start():text.index(' :=',match.start())] for match in re.finditer(r'^theorem ',text,re.M)]
assert signatures(old) == signatures(new) and len(signatures(new)) == 5
assert re.findall(r'^def [^\n]+',old,re.M) == re.findall(r'^def [^\n]+',new,re.M)
for name in ['generate.py','prepare.py','prepare_recipe.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','generated/' + MODULE + '.lean','project/ShielddSecurity/' + MODULE + '.lean','runs/01-' + MODULE + '/stdout.txt']:
    add(REJECTED / name, 'rejected-01/' + name, 'original compiler failure; whole attempt zero credit')

add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'EXACT_MAX_U64_BYTES_DERIVE_SEMANTIC_OVERFLOW_AND_WHOLE_ORDINARY_REFUSAL_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 1, 'fresh_theorem_audits': 5,
    'fresh_complete_public_audits': 6, 'fresh_audits': fresh, 'inherited_complete_public_audits': 277,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 1, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' All six declarations have complete type/axiom reports; one definition and five theorem conclusions are identical to the rejected predecessor. The maintained generator fixed only a codec projection proof step, and successful generated source was independently reproduced byte-exact in a fresh owned directory. The rejected compiler attempt retains zero credit. Qualified codec predecessor and its rejected zero-credit history are exact inherited packet references. No new native control or Rust semantics refinement.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-ordinary-max-count-endpoint-v1', 'entries': records,
    'fresh_audits': 6, 'inherited_audits': 277, 'inherited_reference': reference,
    'object_bytes_in_archive': 0, 'toolchain_bytes_in_archive': 0,
    'native_test_credit': 0, 'negative_control_credit': 0, 'certification': False, 'scope': review['scope']}
data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
(ROOT / 'manifest.json').write_bytes(data)
payload.append(('manifest.json', data))
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for name, data in sorted(payload):
        info = tarfile.TarInfo(name)
        info.size, info.mode, info.mtime = len(data), 0o644, 0
        tar.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == len(payload)
    assert all(tar.extractfile(name).read() == data for name, data in payload)
assert all(pin(r['original']['path']) == r['original'] for r in records)
print(json.dumps({'archive': pin(archive), 'manifest': pin(ROOT / 'manifest.json'), 'review': pin(ROOT / 'review.json'),
    'entries': len(records), 'members': len(payload), 'fresh_audits': 6, 'inherited_audits': 277,
    'native_test_credit': 0, 'certification': False}))
