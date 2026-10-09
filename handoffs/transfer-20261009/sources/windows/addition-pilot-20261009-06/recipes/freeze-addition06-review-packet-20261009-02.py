from pathlib import Path
import base64, gzip, hashlib, json, re, subprocess

local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
dest = local / 'addition06-review-packet-20261009-02'
assert not dest.exists(), 'fresh frozen packet required'
dest.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
files = {}
def copy(p, rel):
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(p.read_bytes())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}
def write(rel, value):
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((json.dumps(value, indent=2) + '\n').encode())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

stem = 'windows-addition-pilot-20261009-06'
kernel = diag / (stem + '-kernel')
source = diag / (stem + '-source')
boundary = diag / 'quiescent-addition-pilot-boundary-2026100906'
assert (kernel / 'complete.txt').exists() and (kernel / 'end.txt').exists()
assert (kernel / 'exit.txt').read_text().strip() == '0'
assert (boundary / 'complete.txt').exists() and (boundary / 'exit.txt').read_text().strip() == '0'
assert (boundary / 'native-resume-disposition.txt').read_text().strip().startswith('not-applicable:')
m = load(source / 'manifest.json')
modules = {}
for name in m['order']:
    leaf = kernel / name
    a = load(leaf / 'audit.json')
    assert a['full_types_checked'] and (leaf / 'exit.txt').read_text().strip() == '0'
    assert (leaf / 'end.txt').exists() and not (leaf / 'stop.txt').exists()
    assert sha(kernel / 'project' / m['sources'][name]['lean_relative_path']) == m['audited_candidates'][name] == a['candidate_sha256']
    assert sha(repo / 'circuits/ShielddSecurity' / (name + '.lean')) == m['sources'][name]['sha256']
    assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in a['axioms'].values())
    text = (leaf / 'stdout.txt').read_text(encoding='utf-8-sig')
    assert not re.search(r'\b(?:error|sorryAx)\b', text + (leaf / 'stderr.txt').read_text(encoding='utf-8-sig'))
    copy(leaf / 'stdout.txt', 'review-audit-text/' + name + '.txt')
    copy(leaf / 'audit.json', 'audits/' + name + '.json')
    copy(source / (name + '-audited.lean'), 'audited-source/' + name + '.lean')
    modules[name] = {'audit': a, 'actual_exit': 0, 'stdout_sha256': sha(leaf / 'stdout.txt'), 'stderr_sha256': sha(leaf / 'stderr.txt'), 'start': (leaf / 'start.txt').read_text().strip(), 'end': (leaf / 'end.txt').read_text().strip()}
assert sum(v['audit']['audits'] for v in modules.values()) == 17
for p in [source / 'manifest.json', kernel / 'recipe.json', kernel / 'external-overlay.json', boundary / 'admission.json']:
    copy(p, 'inputs/' + p.name)
for name in ['EdwardsAdditionPilot01', 'ConcretePointAdditionPilot01', 'EdwardsTorsionAlgebra01', 'ConcretePointOperationRows01', 'ConcretePointCoordinates01', 'ConcreteOriginAdditionPilot01', 'EdwardsExceptionalClassification01']:
    copy(repo / 'circuits/ShielddSecurity' / (name + '.lean'), 'maintained-source/' + name + '.lean')
for p in [Path(__file__), local / 'prepare-addition-pilot-20261009-06.py', local / 'prepare-windows-concrete-edwards-20261009-01.py', local / 'inspect-addition-pilot-closure-20261009-06.py', local / 'inspect-field-concrete-closure-20261009-01.py', local / 'compose-addition-pilot-cache-20261009-06.py', local / 'invoke-quiescent-narrow-kernel-20261009-01.ps1', diag / ('root-' + stem + '.ps1'), diag / ('audit-' + stem + '.py'), diag / 'native-host-memory-api-01.ps1']:
    copy(p, 'recipes/' + p.name)
dependencies = []
for item in m['reused']:
    original = Path(item['original_source'])
    assert sha(original) == item['original_source_sha256']
    assert sha(Path(item['source'])) == item['source_sha256']
    assert sha(Path(item['object'])) == item['object_sha256']
    for sidecar in item['sidecars']:
        assert sha(Path(sidecar['path'])) == sidecar['sha256']
    try:
        canonical = original.relative_to(repo).as_posix()
    except ValueError:
        candidates = [repo / 'circuits/ShielddSecurity' / original.name] + list((repo / 'handoffs/transfer-20261009/sources').rglob(original.name))
        candidates = [p for p in candidates if p.exists()]
        matches = [p for p in candidates if sha(p) == item['original_source_sha256']]
        assert matches, (item['name'], item['original_source_sha256'])
        canonical = matches[0].relative_to(repo).as_posix()
    dependencies.append(dict(item, canonical_repository_reference=canonical))
for path, digest in m['frozen_import_receipts'].items():
    assert sha(Path(path)) == digest
write('dependency-resolution.json', dependencies)
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
assert head == '0c270fdf940dc929e642a8bffaf9ae63fe5b7250'
receipt = {'actual_publication_checkout_head': head, 'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'mathlib_sha': 'c5ea00351c28e24afc9f0f84379aa41082b1188f', 'lean_version': '4.30.0', 'modules': modules, 'fresh_modules': 2, 'declaration_audits': 17, 'new_negative_control_credit': 0, 'recipe': load(kernel / 'recipe.json'), 'source_manifest_sha256': sha(source / 'manifest.json'), 'qualified_external_identities_sha256': sha(kernel / 'qualified-external-identities.json'), 'external_before_sha256': sha(kernel / 'external-before.json'), 'native_resume': 'not applicable: native controller absent; no suspension or resume performed', 'batch_actual_exit': 0, 'batch_start': (kernel / 'start.txt').read_text().strip(), 'batch_end': (kernel / 'end.txt').read_text().strip(), 'proved_scope': ['generic Edwards addition closure, identity, commutativity, inverse, torsion formula', 'concrete Mathlib negation transport', 'identity and inverse addition images'], 'open': ['general addition homomorphism', 'StandardCurveModel', 'scalar trace', 'point order', 'cardinality', 'native codec', 'full Transfer'], 'other_maintained_sources': {'EdwardsTorsionAlgebra01': 'fresh03 passed 9 audits separately; no torsion Point transport claim in addition06 receipt', 'ConcretePointOperationRows01': 'prepared01 starting separately; zero sealed operation-row credit at freeze', 'ConcretePointCoordinates01': 'source only UNRUN', 'ConcreteOriginAdditionPilot01': 'source only UNRUN', 'EdwardsExceptionalClassification01': 'source only UNRUN'}, 'failed_addition_attempts': {'01': 'compiler failure; zero credit', '02': 'source hash gate before Lean; zero credit', '03': 'concrete compiler failure; batch zero credit', '04': 'memory admission before Lean; zero credit', '05': 'concrete unknown injEq.mpr constant; batch zero credit'}, 'inherited_metadata_disposition': 'Prepared import manifest retains historical parent metadata. This receipt reports actual current HEAD separately; no certification follows from historical metadata or hashes.'}
write('receipt.json', receipt)
write('manifest.json', {'kind': 'Frozen local review packet; no commit, publication, or push', 'files': dict(files), 'review_audit_text_disposition': 'Small successful type/axiom outputs for independent local review, not intended as committed logs', 'full_transfer': 'OPEN'})
payload = json.dumps({'files': {rel: base64.b64encode((dest / rel).read_bytes()).decode() for rel in files}}, separators=(',', ':')).encode()
packed = gzip.compress(payload, mtime=0)
archive = local / 'addition06-review-packet-20261009-02.json.gz'
assert not archive.exists()
archive.write_bytes(packed)
print(json.dumps({'marker': 'TRANSFER_ADDITION06_REVIEW_PACKET_V1', 'encoding': 'gzip-json-files-base64', 'sha256': sha(archive), 'bytes': len(packed), 'manifest_sha256': sha(dest / 'manifest.json'), 'payload_base64': base64.b64encode(packed).decode()}, separators=(',', ':')))
