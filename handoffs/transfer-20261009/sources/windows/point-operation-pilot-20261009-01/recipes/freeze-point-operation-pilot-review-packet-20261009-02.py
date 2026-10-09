from pathlib import Path
import argparse, base64, gzip, hashlib, json, re, subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--pilot-run', required=True, choices=['01'])
args = parser.parse_args()
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
dest = local / 'point-operation-pilot-review-packet-20261009-02'
assert not dest.exists(), 'fresh frozen review packet required'
dest.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
files = {}

def copy(p, rel):
    target = dest / rel
    if rel in files:
        assert sha(p) == files[rel]['sha256']
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(p.read_bytes())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

def write(rel, value):
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((json.dumps(value, indent=2) + '\n').encode())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}

specs = [('point-operation-pilot', args.pilot_run, 'point-operation-pilot', ['ConcreteIntegerCertificates01', 'ConcretePointOperationPilot01'])]

modules, batches, dependencies = {}, {}, {}
tracked = set(subprocess.check_output(['git', '-C', str(repo), 'ls-files'], text=True).splitlines())
for prefix, run, boundary_prefix, expected in specs:
    stem = f'windows-{prefix}-20261009-{run}'
    source, kernel = diag / (stem + '-source'), diag / (stem + '-kernel')
    boundary = diag / f'quiescent-{boundary_prefix}-boundary-20261009{run}'
    for root in [kernel, boundary]:
        assert (root / 'complete.txt').exists() and (root / 'end.txt').exists()
        assert (root / 'exit.txt').read_text().strip() == '0'
    assert (boundary / 'native-resume-disposition.txt').read_text().startswith('not-applicable:')
    m = load(source / 'manifest.json')
    assert m == load(kernel / 'manifest.json')
    assert set(m['order']) == set(expected)
    recipe = load(kernel / 'recipe.json')
    assert recipe['memory_MiB'] == 1536 and recipe['finite_seconds_per_module'] == 240 and recipe['threads'] == 1
    guard = diag / ('root-' + stem + '.ps1')
    auditor = diag / ('audit-' + stem + '.py')
    assert sha(guard) == recipe['guard_sha256'].lower()
    assert sha(auditor) == recipe['audit_sha256'].lower()
    for name in expected:
        leaf = kernel / name
        a = load(leaf / 'audit.json')
        assert a['full_types_checked'] and (leaf / 'exit.txt').read_text().strip() == '0'
        assert (leaf / 'end.txt').exists() and not (leaf / 'stop.txt').exists()
        assert sha(kernel / 'project' / m['sources'][name]['lean_relative_path']) == m['audited_candidates'][name] == a['candidate_sha256']
        original = repo / 'circuits/ShielddSecurity' / (name + '.lean')
        assert sha(original) == m['sources'][name]['sha256'] == a['original_source_sha256']
        output = (leaf / 'stdout.txt').read_text(encoding='utf-8-sig')
        stderr = (leaf / 'stderr.txt').read_text(encoding='utf-8-sig')
        assert not re.search(r'\b(?:error|sorryAx)\b', output + stderr)
        reports = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", output)
        reports += [(n, '') for n in re.findall(r"'([\w.]+)' does not depend on any axioms", output)]
        assert len(reports) == a['audits'] == len(m['expected_theorems_by_module'][name])
        assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in a['axioms'].values())
        for full, used in reports:
            assert set(re.findall(r'[\w.]+', used)) <= {'propext', 'Classical.choice', 'Quot.sound'}
            assert re.search(r'(?:^|\n)@?' + re.escape(full) + r'\s*:', output)
        copy(original, 'maintained-source/' + name + '.lean')
        copy(source / (name + '-audited.lean'), 'audited-source/' + name + '.lean')
        copy(leaf / 'audit.json', 'audits/' + name + '.json')
        copy(leaf / 'stdout.txt', 'review-audit-text/' + name + '.txt')
        modules[name] = {'batch': stem, 'audit': a, 'actual_exit': 0,
            'stdout_sha256': sha(leaf / 'stdout.txt'), 'stderr_sha256': sha(leaf / 'stderr.txt'),
            'start': (leaf / 'start.txt').read_text().strip(), 'end': (leaf / 'end.txt').read_text().strip()}
    for item in m['reused']:
        assert sha(Path(item['original_source'])) == item['original_source_sha256']
        assert sha(Path(item['source'])) == item['source_sha256']
        assert sha(Path(item['object'])) == item['object_sha256']
        for sidecar in item['sidecars']:
            assert sha(Path(sidecar['path'])) == sidecar['sha256']
        key = (item['name'], item['original_source_sha256'])
        candidates = [repo / 'circuits/ShielddSecurity' / Path(item['original_source']).name]
        candidates += list((repo / 'handoffs/transfer-20261009/sources').rglob(Path(item['original_source']).name))
        matches = [p for p in candidates if p.exists() and sha(p) == item['original_source_sha256']]
        assert matches, key
        canonical = matches[0].relative_to(repo).as_posix()
        reference = dict(item, repository_reference=canonical,
            reference_disposition='tracked at actual publication HEAD' if canonical in tracked else 'maintained untracked proof source included in this review packet')
        if canonical not in tracked:
            copy(matches[0], 'maintained-source/' + matches[0].name)
        dependencies.setdefault(key, reference)
        assert dependencies[key]['source_sha256'] == reference['source_sha256']
    for path, digest in m['frozen_import_receipts'].items():
        assert sha(Path(path)) == digest
    for p in [source / 'manifest.json', kernel / 'recipe.json', kernel / 'external-overlay.json', boundary / 'admission.json']:
        copy(p, 'inputs/' + stem + '/' + p.name)
    copy(guard, 'recipes/' + guard.name)
    copy(auditor, 'recipes/' + auditor.name)
    for p in [local / f'compose-{prefix}-cache-20261009-{run}.py', local / f'inspect-{prefix}-closure-20261009-{run}.py']:
        copy(p, 'recipes/' + p.name)
    batches[stem] = {'recipe': recipe, 'scope': m['scope'], 'actual_exit': 0,
        'source_manifest_sha256': sha(source / 'manifest.json'),
        'qualified_external_identities_sha256': sha(kernel / 'qualified-external-identities.json'),
        'external_before_sha256': sha(kernel / 'external-before.json'),
        'start': (kernel / 'start.txt').read_text().strip(), 'end': (kernel / 'end.txt').read_text().strip()}

assert len(modules) == 2 and sum(v['audit']['audits'] for v in modules.values()) == 15
for filename in ['prepare-windows-concrete-edwards-20261009-01.py',
 'inspect-field-concrete-closure-20261009-01.py','compose-concrete-point-cache-20261009-05.py',
 'invoke-quiescent-narrow-kernel-20261009-01.ps1','prepare-point-operation-pilot-20261009-01.py',
 'generate-concrete-point-operation-pilot-20261009-01.py','generate-concrete-point-operation-pilot-20261009-02.py']:
 copy(local/filename,'recipes/'+filename)
copy(diag/'native-host-memory-api-01.ps1','recipes/native-host-memory-api-01.ps1')
copy(Path(__file__),'recipes/'+Path(__file__).name)
record=load(local/'point-operation-pilot-generation-20261009-02.json')
assert record['source_sha256']==modules['ConcretePointOperationPilot01']['audit']['original_source_sha256']
assert record['producer_sha256']==sha(local/'generate-concrete-point-operation-pilot-20261009-02.py')
assert len(record['integer_certificates'])==9
copy(local/'point-operation-pilot-generation-20261009-02.json','generation-inputs/point-operation-pilot-generation-20261009-02.json')
candidate=repo/'handoffs/transfer-20261009/sources/parent/weierstrass-order-inputs01/candidate.json'
assert sha(candidate)==record['candidate_sha256']=='028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
write('generation-inputs/candidate-reference.json', {'repository_reference':candidate.relative_to(repo).as_posix(),'sha256':sha(candidate),'bytes':candidate.stat().st_size,'disposition':'Exact tracked input already available to parent; not duplicated in this compact successor','selected_step_index':1,'selected_step':load(candidate)['steps'][1],'base':load(candidate)['base'],'p':load(candidate)['p'],'runtime_sha':load(candidate)['runtime_sha']})
accepted=repo/'handoffs/transfer-20261009/receipts/windows/standard-curve-model-20261009-01.json'
write('inherited/standard-curve-model-reference.json',{'repository_reference':accepted.relative_to(repo).as_posix(),'sha256':sha(accepted),'bytes':accepted.stat().st_size,'disposition':'Published independently reviewed prior result; exact canonical reference, not duplicated'})
for name in ['admission.json','native-resume-disposition.txt','start.txt','end.txt','complete.txt','exit.txt']:
 copy(boundary/name,'boundary/'+name)
for name in expected:
 copy(kernel/name/'memory.txt','resource-samples/'+name+'.txt')
runtime=Path('C:/src/shieldd-pr160-844389ee')
assert subprocess.check_output(['git','-C',str(runtime),'rev-parse','HEAD'],text=True).strip()=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert not subprocess.check_output(['git','-C',str(runtime),'status','--porcelain'],text=True).strip()
write('dependency-resolution.json', list(dependencies.values()))
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
assert head == '54858cdee55575b1b5dc7fcf23ead977844ea61e'
receipt = {'actual_publication_checkout_head': head,
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'mathlib_sha': 'c5ea00351c28e24afc9f0f84379aa41082b1188f', 'lean_version': '4.30.0',
    'fresh_modules': 2, 'declaration_audits': 15, 'modules': modules, 'batches': batches,
    'new_negative_control_credit': 0, 'native_resume': 'not applicable: native controller absent',
    'transport_disposition':'Full new sources, audits, successful type/axiom text, recipes and dependencies retained; existing canonical candidate and accepted model represented by exact repository references',
    'actual_kernel_execution_checkout_head': '9bd2eaf60dad73c68cfa36563a8472f2be54670e',
    'proved_scope': ['integer-multiple equality and nonzero certificate consumers over the exact field',
        'canonical candidate base is on the actual Mathlib curve',
        'first concrete actual Point doubling and addition with derived output curve membership',
        'actual scalar prefix three equals the exact candidate output point'],
    'open': ['remaining 367 operations of the 369-operation scalar trace', 'point order',
        'cardinality', 'native generator correspondence', 'full Transfer G2-G5/G7 obligations', 'full Transfer'],
    'failed_attempts': {'point-operation-pilot-generation01':
        'Assertion rejected unconverted addition denominator inverse orientation before writing Lean source; no kernel launch and zero proof/control credit'},
    'prior_standard_model': {'publication_head':head,'fresh_modules':14,'declaration_audits':54,
        'receipt':'handoffs/transfer-20261009/receipts/windows/standard-curve-model-20261009-01.json',
        'disposition':'Published independently reviewed prior result; no repeated proof credit'},
    'inherited_metadata_disposition': 'Prepared manifests retain historical parent metadata; actual HEAD is reported separately. Hashes establish identity, not semantic correspondence.'}
write('receipt.json', receipt)
write('manifest.json', {'kind': 'Frozen compact successor review packet; canonical candidate and accepted model referenced exactly; no commit or push', 'files': dict(files),
    'review_audit_text_disposition': 'Successful full type and axiom text for independent review; omit from committed publication',
    'full_transfer': 'OPEN'})
payload = json.dumps({'files': {rel: base64.b64encode((dest / rel).read_bytes()).decode() for rel in files}}, separators=(',', ':')).encode()
archive = dest.with_suffix('.json.gz')
assert not archive.exists()
archive.write_bytes(gzip.compress(payload, mtime=0))
print(json.dumps({'marker': 'TRANSFER_POINT_OPERATION_PILOT_REVIEW_PACKET_V1', 'archive': str(archive),
    'encoding': 'gzip-json-files-base64', 'sha256': sha(archive), 'bytes': archive.stat().st_size,
    'manifest_sha256': sha(dest / 'manifest.json'), 'files': len(files), 'fresh_modules': 2,
    'declaration_audits': 15, 'full_transfer': 'OPEN'}))
