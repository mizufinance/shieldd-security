"""Seal the successfully-loaded SCT branch and exact manager callback join."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-nullifier-consensus-limits-20261011-02'
CHECKPOINT = DIAG / 'transfer-nullifier-consensus-limits-checkpoint-20261011-02'
MODULE = 'TransferNullifierConsensusLimits01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-nullifier-consensus-limits-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('sct_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / ('runs/01-' + MODULE + '/stdout.txt')
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 7 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 38 and len(pool['inherited_public_reports']) == 379
manager_endpoint = DIAG / 'transfer-whole-durable-readback-endpoint-20261011-02'
manager_archive = manager_endpoint / 'portable-windows-whole-durable-readback-endpoint01.tar.xz'
assert pin(manager_archive)['sha256'] == '45ead05e5c8b9ad84385ca2535dc55b78acc21756c84db2058c54729b002e997'
with tarfile.open(manager_archive, 'r:xz') as tar:
    manager_review = json.loads(tar.extractfile('review.json').read())
    manager_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    manager_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    manager_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    manager_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    manager_stdout = tar.extractfile('reports/fresh-11-complete-declarations.txt').read().decode()
    manager_reports = m.audit(manager_stdout, manager_plan['targets'][0]['audit_names'])
assert len(manager_reports) == 11 and manager_reports == manager_review['fresh_audits'] == manager_events[-1]['result']['audits']
combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}
manager_selected = manager_pool['selected'] + [{'module': 'TransferWholeDurableReadback01',
    'source': manager_plan['targets'][0]['source'], 'object': manager_events[-1]['result']['objects'][0]}]
assert len(combined_reports) == 379 and combined_reports == pool['inherited_public_reports']
assert len(manager_selected) == 38
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
reference = {'whole_durable_readback': {'archive': pin(manager_archive), 'manifest': pin(manager_endpoint / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 11},
    'ancestors': manager_reference, 'complete_owned_modules': 38, 'inherited_complete_reports': 379,
    'all_inherited_source_object_and_full_report_identities_verified': True,
    'scope': 'Exact thirty-eight-module closure through whole typed current Reader/verified durable status, retained pending encoding and both whole body/index/deferred contexts, with all 379 inherited complete reports; Readback seventeen reports included exactly once. No ancestors replayed here.'}
dump(ROOT / 'inherited-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact successful source and unchanged strict guards')
add(CURRENT / ('generated/' + MODULE + '.lean'), 'source/ShielddSecurity/' + MODULE + '.lean', 'generated exact consensus capacity, supported word maxima, derived bound and three whole-delivery wrappers')
add(stdout, 'reports/fresh-7-complete-declarations.txt', 'all raw full types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'complete thirty-eight-module first import root; no object bytes')
add(ROOT / 'inherited-reference.json', 'context/inherited-reference.json', 'verified 379 inherited reports and exact source associations')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean runtime identities preserved')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
runtime_rows = {row['path']: row for row in mapping['runtime_sources']}
for producer in ['transfer-nullifier-batch-source-20261011-02', 'transfer-raw-effects-source-20261011-04']:
    association_file = DIAG / producer / 'source-mapping.json'
    association_pin = pin(association_file)
    assert association_pin in plan['pins']
    association = json.loads(association_file.read_bytes())
    assert association['runtime_sha'] == mapping['runtime_sha']
    add(association_file, 'context/ancestor-source-associations/' + producer + '.json', 'unchanged source association already pinned in the qualified plan; not semantic proof')
    for row in association['runtime_sources']:
        assert pin(row['path']) == row
        assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
        runtime_rows[row['path']] = row
    for interface in association.get('interfaces', []):
        if interface not in mapping['interfaces']:
            mapping['interfaces'].append(interface)
mapping['runtime_sources'] = list(runtime_rows.values())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
    relative = Path(row['path']).relative_to(Path('C:/src/shieldd-pr160-844389ee')).as_posix()
    add(row['path'], 'runtime/' + relative, 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')
add(Path(__file__), 'assemble.py', 'exact assembly source')
review = {'status': 'EXACT_SOURCE_NULLIFIER_CONSENSUS_CAPACITY_DISCHARGES_WHOLE_DELIVERY_WORD_BOUND_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 3, 'fresh_theorem_audits': 4,
    'fresh_complete_public_audits': 7, 'fresh_audits': fresh, 'inherited_complete_public_audits': 379,
    'inherited_reference': reference, 'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'interfaces': mapping['interfaces'], 'runtime_sha': mapping['runtime_sha'],
    'native_test_credit': 0, 'negative_control_credit': 0, 'rejected_attempts': 0, 'rejected_proof_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' All three generated definitions and four theorems have complete original type/axiom reports. Exact source literal/qualified signatures and independent identical generated bytes verified. The arithmetic bound is proved for explicitly selected 32/64-bit word width; concrete native representation remains separate. No generated Lean or evidence hand-edited.'}
dump(ROOT / 'review.json', review)
regen = DIAG / 'transfer-nullifier-consensus-limits-regeneration-20261011-02'
original_generation = json.loads((CURRENT / 'generation.json').read_bytes())
regenerated = json.loads((regen / 'generation.json').read_bytes())
generated_source = CURRENT / ('generated/' + MODULE + '.lean')
assert original_generation['output'] == pin(generated_source)
assert regenerated['output'] == pin(regen / ('generated/' + MODULE + '.lean'))
assert generated_source.read_bytes() == (regen / ('generated/' + MODULE + '.lean')).read_bytes()
assert original_generation['generator'] == regenerated['generator'] == pin(CURRENT / 'generate.py')
assert all(original_generation[key] == regenerated[key] for key in ['capacity_literal', 'capacity', 'supported_widths'])
for row in original_generation['runtime_sources'] + original_generation['upstream_contract_sources']:
    assert pin(row['path']) == row and row in plan['pins']
for name in ['generate.py', 'generation.json']:
    add(CURRENT / name, 'qualified/' + name, 'maintained exact pinned consensus-capacity/qualified-contract generator; no hand-edited output')
add(regen / 'generation.json', 'regeneration/generation.json', 'independent byte-exact generated source identity')
add(regen / ('generated/' + MODULE + '.lean'), 'regeneration/ShielddSecurity/' + MODULE + '.lean', 'independent identical generated Lean source')
failed = DIAG / 'transfer-nullifier-consensus-limits-20261011-01'
failed_plan = json.loads((failed / 'plan.json').read_bytes())
failed_events = [json.loads(line) for line in (failed / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
assert not (failed / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
old_source = (failed / ('generated/' + MODULE + '.lean')).read_text()
new_source = (CURRENT / ('generated/' + MODULE + '.lean')).read_text()
normalized = new_source.replace('set_option autoImplicit false\n', '')
for namespace, identifier in [('TransferWholeDurableReadback01', 'installReader'), ('TransferWholeDurableReadback01', 'currentReader'),
    ('TransferCurrentPendingReplay01', 'withPending')]:
    normalized = normalized.replace(namespace + '.' + identifier, identifier)
assert normalized == old_source
for name in ['generate.py', 'generation.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'generated/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean',
    'runs/01-' + MODULE + '/stdout.txt']:
    row = pin(failed / name)
    assert row in plan['pins']
    add(failed / name, 'rejected-01/' + name, 'failed generator helper qualification predecessor, whole proof/control credit zero; no generated source/evidence patched')
failed_regen = DIAG / 'transfer-nullifier-consensus-limits-regeneration-20261011-01'
for name in ['generation.json', 'generated/' + MODULE + '.lean']:
    assert pin(failed_regen / name) in plan['pins']
    add(failed_regen / name, 'rejected-01-regeneration/' + name, 'original exact regeneration for rejected generation; zero proof/control credit')
stopped_sealer = DIAG / 'transfer-nullifier-consensus-limits-endpoint-20261011-01'
assert not (stopped_sealer / 'manifest.json').exists() and not (stopped_sealer / 'portable-windows-nullifier-consensus-limits-endpoint01.tar.xz').exists()
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped_sealer / name, 'unexecuted-sealer-01/' + name, 'unexecuted failed predecessor sealer setup, zero proof/control credit')
review['rejected_attempts'] = 1
review['rejected_attempt'] = {'plan': pin(failed / 'plan.json'), 'compiler_result': failed_events[-1]['result'],
    'proof_credit': 0, 'control_credit': 0, 'successor_diff': 'Maintained generator qualifies exactly three original helper names and disables autoImplicit. Every source declaration/premise/conclusion otherwise byte-identical after namespace normalization.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'complete current audit and explicit load/clone/tree/panic limits')
manifest = {'schema': 'transfer-nullifier-consensus-limits-endpoint-v1', 'entries': records,
    'fresh_audits': 7, 'inherited_audits': 379, 'inherited_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 7, 'inherited_audits': 379,
    'native_test_credit': 0, 'certification': False}))
