"""Seal corrected FeeFunding names and exact prior-packet associations."""
import hashlib
import importlib.util
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
CURRENT = DIAG / 'transfer-raw-effects-source-20261011-04'
PRIOR = DIAG / 'transfer-raw-effects-source-20261011-03'
PRIOR_ENDPOINT = DIAG / 'transfer-raw-effects-endpoint-20261011-01'
CHECKPOINT = DIAG / 'transfer-raw-effects-context-checkpoint-20261011-01'

def pin(p):
    p = Path(p)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(p, obj):
    p.write_bytes((json.dumps(obj, indent=2, sort_keys=True) + '\n').encode())

archive = ROOT / 'portable-windows-raw-effects-context-endpoint01.tar.xz'
assert not archive.exists() and not (ROOT / 'manifest.json').exists()
spec = importlib.util.spec_from_file_location('context_complete_auditor', CURRENT / 'execute_bounded.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
plan = json.loads((CURRENT / 'plan.json').read_bytes())
events = [json.loads(s) for s in (CURRENT / 'events.jsonl').read_text().splitlines()]
assert len(events) == 2 and events[-1]['result']['status'] == 'passed'
stdout = CURRENT / 'runs/01-TransferRawEffectsSource01/stdout.txt'
fresh = m.audit(stdout.read_text(), plan['targets'][0]['audit_names'])
assert len(fresh) == 27 and fresh == events[-1]['result']['audits']
assert pin(stdout) == events[-1]['result']['stdout']
for obj in events[-1]['result']['objects']:
    assert pin(obj['path']) == obj
prior_archive = PRIOR_ENDPOINT / 'portable-windows-raw-effects-endpoint01.tar.xz'
assert pin(prior_archive)['sha256'] == 'ac82437a811bb5fee118e832fe970f22a2bc8afc3d14d8783712e0ec3e7ca044'
prior_manifest = json.loads((PRIOR_ENDPOINT / 'manifest.json').read_bytes())
with tarfile.open(prior_archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == len(prior_manifest['entries']) + 1 == 36
    assert tar.extractfile('manifest.json').read() == (PRIOR_ENDPOINT / 'manifest.json').read_bytes()
    for row in prior_manifest['entries']:
        data = tar.extractfile(row['archive_path']).read()
        assert len(data) == row['original']['bytes'] and hashlib.sha256(data).hexdigest() == row['original']['sha256']
        assert pin(row['original']['path']) == row['original']
    old_source = tar.extractfile('source/ShielddSecurity/TransferRawEffectsSource01.lean').read()
    old_stdout = tar.extractfile('reports/fresh-27-complete-declarations.txt').read()
    prior_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    prior_audits = m.audit(old_stdout.decode(), prior_plan['targets'][0]['audit_names'])
    prior_review = json.loads(tar.extractfile('review.json').read())
assert len(prior_audits) == 27 and prior_audits == prior_review['fresh_audits']
renames = {'regulated_skips_volume_tail': 'fee_funding_skips_volume_tail',
    'regulated_success_retains_reshape_cache': 'fee_funding_success_retains_reshape_cache'}
corrected_source = old_source.decode()
for before, after in renames.items():
    corrected_source = corrected_source.replace(before, after)
assert corrected_source.encode() == Path(plan['targets'][0]['source']['path']).read_bytes()
prefix = 'ShielddSecurity.TransferRawEffectsSource01.'
unchanged = {n: a for n, a in prior_audits.items() if n not in {prefix + n for n in renames}}
assert len(unchanged) == 25 and all(fresh[n] == a for n, a in unchanged.items())
for before, after in renames.items():
    assert prior_audits[prefix + before]['axioms'] == fresh[prefix + after]['axioms']
pool = json.loads(Path(plan['owned_import_pool']['path']).read_bytes())
assert pool['objects'] == 4 and len(pool['inherited_public_reports']) == 57
prior_pool = json.loads(Path(prior_plan['owned_import_pool']['path']).read_bytes())
assert pool['inherited_public_reports'] == prior_pool['inherited_public_reports']
for a, b in zip(pool['selected'], prior_pool['selected'], strict=True):
    assert a['module'] == b['module'] and a['source'] == b['source'] and a['object'] == b['object']
    for k in ['source', 'object', 'copy']:
        assert pin(a[k]['path']) == a[k]
assert plan['external_floor'] == prior_plan['external_floor']
reference = {'prior': {'archive': pin(prior_archive), 'manifest': pin(PRIOR_ENDPOINT / 'manifest.json'),
    'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE',
    'all_35_original_entries_and_archive_members_reverified': True},
    'prior_27_reports': prior_audits, 'inherited_57_reports': pool['inherited_public_reports'],
    'all_four_owned_sources_objects_and_original_inputs_preserved': True,
    'complete_core_floor': plan['external_floor'], 'core_floor_original_reference': prior_review['inherited_reference']['core_floor'],
    'program_definitions_and_all_theorem_premises_conclusions_unchanged': True,
    'declaration_name_changes': renames, 'unchanged_full_type_and_axiom_reports': 25,
    'prior_report_new_credit': 0, 'native_credit': 0}
dump(ROOT / 'prior-reference.json', reference)
records, payload = [], []

def add(p, name, role):
    p = Path(p)
    assert name not in {n for n, _ in payload}
    payload.append((name, p.read_bytes()))
    records.append({'archive_path': name, 'original': pin(p), 'role': role})

for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:
    add(CURRENT / name, 'qualified/' + name, 'exact corrected source and unchanged guard provenance')
add(CURRENT / 'handwritten/TransferRawEffectsSource01.lean', 'source/ShielddSecurity/TransferRawEffectsSource01.lean', 'maintained source with correct FeeFunding names')
add(stdout, 'reports/fresh-27-complete-declarations.txt', 'all full corrected declaration types and permitted axioms')
add(plan['owned_import_pool']['path'], 'context/owned-composition-review.json', 'exact complete four-module import root; no object bytes')
add(ROOT / 'prior-reference.json', 'context/prior-reference.json', 'lossless original associations and explicit prior labeling correction')
mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())
for row in mapping['runtime_sources']:
    assert pin(row['path']) == row
new_runtime = next(r for r in mapping['runtime_sources'] if r['path'].replace('\\', '/').endswith('/volume_accumulator.rs'))
add(new_runtime['path'], 'runtime/volume_accumulator.rs', 'exact pinned enum snapshot Ordinary | FeeFunding; other six snapshots referenced without duplicate transport')
for name in ['preservation_check.py', 'preservation.json']:
    add(CHECKPOINT / name, 'preservation/' + name, 'all protected/foreign/main/clean-runtime identities preserved')
add(DIAG.parent.parent / 'shieldd.lock', 'context/shieldd.lock', 'exact full runtime SHA')
add(Path(__file__), 'assemble.py', 'exact transport assembly source')
review = {'status': 'RAW_EFFECT_FEE_FUNDING_CONTEXT_LABELS_CORRECTED_AND_ALL_27_REPORTS_QUALIFIED',
    'fresh_sources': 1, 'fresh_definition_audits': 12, 'fresh_theorem_audits': 15,
    'fresh_complete_public_audits': 27, 'fresh_audits': fresh, 'inherited_complete_public_audits': 57,
    'prior_reference': reference, 'context': mapping['context'], 'interfaces': mapping['interfaces'],
    'compiler_result': events[-1]['result'], 'plan': pin(CURRENT / 'plan.json'),
    'runtime_sha': mapping['runtime_sha'], 'native_test_credit': 0, 'negative_control_credit': 0,
    'certification': False, 'full_transfer': 'OPEN',
    'scope': mapping['scope'] + ' This successor corrects the historical false-branch labels: false denotes FeeFunding, true denotes Ordinary. Regulated disclosure is not a third TransferProofContext. Executable definitions and all theorem premises/conclusions are byte-identical after just two declaration-name replacements. Prior packet remains immutable with this explicit correction; its rejection/prior-qualified provenance and six runtime snapshots are reverified references, not newly executed or double-counted.'}
dump(ROOT / 'review.json', review)
add(ROOT / 'review.json', 'review.json', 'current complete proof census and explicit correction of prior labels')
manifest = {'schema': 'transfer-raw-effects-context-endpoint-v1', 'entries': records,
    'fresh_audits': 27, 'inherited_audits': 57, 'prior_reference': reference,
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
    'entries': len(records), 'members': len(payload), 'fresh_audits': 27, 'inherited_audits': 57,
    'native_test_credit': 0, 'certification': False}))
