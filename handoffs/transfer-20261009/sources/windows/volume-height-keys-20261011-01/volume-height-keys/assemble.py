"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-volume-height-keys-20261011-01'
CHECKPOINT = DIAG / 'transfer-volume-height-keys-checkpoint-20261011-01'
MODULE = 'TransferVolumeHeightKeys01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-volume-height-keys-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 9 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 19 and len(pool['inherited_public_reports']) == 234
manager_endpoint = DIAG / 'transfer-ordinary-height-endpoint-20261011-01'
manager_archive = manager_endpoint / 'portable-windows-ordinary-height-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '3769f37fa4d3257ce66f2bfc5b9e820f78521c57a375a2478c7719c64749362a'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 5 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferOrdinaryHeightSource01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 234 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 19
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
reference = {'height': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 5},
    'ancestors': manager_reference, 'complete_owned_modules': 19, 'inherited_complete_reports': 234,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact nineteen-module closure through source height read and all-return V framing, with all 234 inherited complete reports. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('portable-source/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'four exact-ASCII key definitions and five finite namespace/projected-key/whole-indexed-success proofs')
add(stdout, 'reports/fresh-9-complete-declarations.txt', 'all raw full types and permitted axioms')
for name in ['generate.py', 'source.lean.in']:
    add(CURRENT / name, 'generator/' + name, 'maintained deterministic LF source generator and finite handwritten proof template')
add(CURRENT / 'generate-rejected-prefix-parser.py', 'pre-admission/generator-original.py', 'ambiguous prefix lookup refused before Lean; zero proof/control credit')
add(CURRENT / ('generated/' + MODULE + '.lean'), 'pre-admission/intermediate-source.lean', 'intermediate unadmitted newline variant; zero kernel credit')
generator_spec = importlib.util.spec_from_file_location('portable_ascii_key_generator', CURRENT / 'generate.py')
generator = importlib.util.module_from_spec(generator_spec)
generator_spec.loader.exec_module(generator)
runtime_root = Path('C:/src/shieldd-pr160-844389ee')
regenerated = generator.render((runtime_root / 'crates/core/component/sct/src/state_key.rs').read_text(),
    (runtime_root / 'crates/core/component/shielded-pool/src/state_key.rs').read_text()).encode('utf-8')
assert regenerated == (CURRENT / ('portable-source/' + MODULE + '.lean')).read_bytes()
assert b'\r' not in regenerated
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete nineteen-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 234 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'ACTUAL_ASCII_KEY_NAMESPACE_SEPARATION_JOINS_WHOLE_ORDINARY_INDEXED_HEIGHT_AND_VOLUME_SUCCESS_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 4, 'fresh_theorem_audits': 5,
    'fresh_complete_public_audits': 9, 'fresh_audits': fresh, 'inherited_complete_public_audits': 234,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 0, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'portable_generated_bytes_verified': True,
    'pre_admission_generator_refusals': 1, 'pre_admission_kernel_credit': 0,
    'scope': mapping['scope'] + ' Nine source declarations qualified in one guarded Lean attempt. Source generator verifies the exact runtime function literals, scopes prefix extraction to volume_nullifiers, and reproduces all admitted LF bytes. Original ambiguous-prefix parser and intermediate newline variant remain preserved and unadmitted. Byte-to-model key projection remains explicit; hashes are identity evidence only, not Rust semantics, native control or certification.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-volume-height-keys-endpoint-v1', 'entries': records,
    'fresh_audits': 9, 'inherited_audits': 234, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 9, 'inherited_audits': 234,
    'native_test_credit': 0, 'certification': False}))
