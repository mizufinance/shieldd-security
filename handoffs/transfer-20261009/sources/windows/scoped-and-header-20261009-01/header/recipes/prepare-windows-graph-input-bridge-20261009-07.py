from pathlib import Path
import ast
import hashlib
import json
import re

root = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
src = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')
stem = 'windows-graph-input-bridge-20261009-07'
out = root / (stem + '-source')
assert not out.exists(), 'fresh preparation required'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
fresh = ['ScalarCompletion', 'CompilerCompletion',
         'TransferCircuitInputSeed', 'TransferCircuitHeaderInputs', 'TransferCircuitHeaderCarrierSeed']
providers = ['semantic-input-recovery-current-project-kernel-3223',
             'source-graph-evaluation-current-project-kernel-3228',
             'compiler-certificate-transport-current-project-kernel-3235',
             'semantic-tail-current-project-kernel-3050',
             'authorization-current-project-kernel-3036']
manifests = {}
for provider in providers:
    batch = root / provider
    assert all((batch / name).exists() for name in ['end.txt', 'complete.txt', 'exit.txt'])
    assert (batch / 'exit.txt').read_text().strip() == '0' and not (batch / 'stop.txt').exists()
    manifests[provider] = load(batch / 'manifest.json')
    assert load(batch / 'recipe.json')['threads'] == 1
    assert load(batch / 'cache-inputs.json')['packages']['mathlib'] == 'c5ea00351c28e24afc9f0f84379aa41082b1188f'

sources, dependency_order = {}, []
def visit(name):
    if name in sources:
        return
    path = src / (name + '.lean')
    raw = path.read_bytes()
    imports = re.findall(r'^import\s+([\w.]+)', raw.decode(), re.M)
    for dep in imports:
        if dep.startswith('ShielddSecurity.'):
            visit(dep.split('.', 1)[1])
    sources[name] = {'path': str(path), 'bytes': len(raw), 'sha256': sha(path), 'imports': imports}
    dependency_order.append(name)
for name in fresh:
    visit(name)

reused, frozen = [], {}
for name in dependency_order:
    if name in fresh:
        continue
    candidates = []
    for provider in providers:
        batch = root / provider
        manifest = manifests[provider]
        source = batch / 'project/ShielddSecurity' / (name + '.lean')
        obj = source.with_suffix('.olean')
        if not source.exists() or sha(source) != sources[name]['sha256'] or not obj.exists():
            continue
        leaf_batch = batch
        visited = set()
        while True:
            assert leaf_batch not in visited and len(visited) < 32, ('finite qualified import ancestry required', name)
            visited.add(leaf_batch)
            leaf = leaf_batch / name
            if (leaf / 'end.txt').exists() and (leaf / 'exit.txt').exists():
                break
            parent_manifest = load(leaf_batch / 'manifest.json')
            records = [x for x in parent_manifest.get('reused', []) if x['name'] == name]
            if len(records) != 1:
                break
            record = records[0]
            assert sha(Path(record['source'])) == record['source_sha256'] and sha(Path(record['object'])) == record['object_sha256']
            assert record['source_sha256'] == sources[name]['sha256'], ('unchanged import ancestry source required', name)
            for path, digest in parent_manifest.get('frozen_import_receipts', {}).items():
                assert sha(Path(path)) == digest, path
                frozen[path] = digest
            frozen[str(leaf_batch / 'manifest.json')] = sha(leaf_batch / 'manifest.json')
            leaf_batch = Path(record['provider_batch'])
        if not (leaf / 'end.txt').exists() or not (leaf / 'exit.txt').exists():
            continue
        if (leaf / 'exit.txt').read_text().strip() != '0' or (leaf / 'stop.txt').exists():
            continue
        logged = (leaf / 'stdout.txt').read_text(encoding='utf-8-sig')
        errors = (leaf / 'stderr.txt').read_text(encoding='utf-8-sig')
        assert not re.search(r'\b(sorryAx|error)\b', logged + errors)
        printed = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", logged)
        printed += [(n, '') for n in re.findall(r"'([\w.]+)' does not depend on any axioms", logged)]
        assert all(set(re.findall(r'[\w.]+', used)) <= {'propext', 'Classical.choice', 'Quot.sound'} for _, used in printed)
        for checked in re.findall(r'^#check @([\w.]+)', source.read_text(), re.M):
            short = checked.split('.')[-1]
            assert any(n.split('.')[-1] == short for n, _ in printed), (provider, name, short, 'actual printed axiom audit required')
            assert re.search(r'(?:^|\n)@?[\w.]*' + re.escape(short) + r'\s*:', logged), (provider, name, short, 'actual full type required')
        for path, digest in manifest.get('frozen_import_receipts', {}).items():
            assert sha(Path(path)) == digest, path
        candidates.append((batch, leaf, source, obj))
    assert candidates, ('exact qualified import required', name)
    batch, leaf, source, obj = candidates[0]
    for path in [source, obj, leaf / 'stdout.txt', leaf / 'stderr.txt', leaf / 'exit.txt',
                 leaf / 'end.txt', batch / 'manifest.json',
                 batch / 'recipe.json', batch / 'cache-inputs.json', batch / 'exit.txt',
                 batch / 'complete.txt', batch / 'end.txt']:
        frozen[str(path)] = sha(path)
    reused.append({'name': name, 'source': str(source), 'source_sha256': sha(source),
                   'object': str(obj), 'object_sha256': sha(obj), 'provider_batch': str(batch),
                   'actual_leaf_exit': 0})

out.mkdir()
expected, candidates = {}, {}
for name, item in sources.items():
    (out / (name + '.lean')).write_bytes(Path(item['path']).read_bytes())
for name in fresh:
    raw = (src / (name + '.lean')).read_bytes()
    assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b', raw)
    names = re.findall(r'^theorem (\w+)', raw.decode(), re.M)
    assert names and len(names) == len(set(names))
    # Audit directives are diagnostic; proof/definition bytes remain unchanged.
    body = re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n', '', raw.decode())
    audits = ''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n' for n in names)
    marker = '\nend ShielddSecurity.' + name
    assert body.count(marker) == 1
    audited = body.replace(marker, audits + marker).encode()
    assert re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n', '', audited.decode()).split() == body.split()
    path = out / (name + '-audited.lean')
    path.write_bytes(audited)
    expected[name] = names
    candidates[name] = sha(path)

scope = ('Construct source input headers and final claimed-statement input, map all 22735 supplied input values symbolically to private columns starting at3, derive committed2/private9 and public1/private22737 links, and construct the Boolean plus three expected binding rows. Remaining 22726 gadget inputs are supplied and not shown legal; exact indexed inclusion, source/compiler instance, all assertion truth, complete assignment and Rust/state correspondence remain OPEN. Four prerequisites are unchanged narrow replays.')
manifest = {'sources': sources, 'order': fresh, 'dependency_order': dependency_order,
            'expected_theorems_by_module': expected, 'audited_candidates': candidates,
            'proof_bytes_changed': False, 'kernel_run': False,
            'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'scope': scope,
            'reused': reused, 'frozen_import_receipts': frozen}
(out / 'manifest.json').write_bytes((json.dumps(manifest, indent=2) + '\n').encode())

auditor = root / ('audit-' + stem + '.py')
assert not auditor.exists()
audit = '''from pathlib import Path
import hashlib,json,re,sys
batch=Path(sys.argv[1]);manifest=json.loads((batch/'manifest.json').read_text(encoding='utf-8-sig'));total=0
for module,names in manifest['expected_theorems_by_module'].items():
 leaf=batch/module;assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
 raw=(batch/'project/ShielddSecurity'/(module+'.lean')).read_bytes();assert hashlib.sha256(raw).hexdigest()==manifest['audited_candidates'][module]
 output=(leaf/'stdout.txt').read_text(encoding='utf-8-sig');stderr=(leaf/'stderr.txt').read_text(encoding='utf-8-sig');assert not re.search(r'\\b(sorryAx|error)\\b',output+stderr)
 prefix='ShielddSecurity.'+module+'.';escaped=re.escape(prefix)
 reports=re.findall("'"+escaped+r"(\\w+)' depends on axioms: \\[([^\\]]*)\\]",output)
 reports += [(n,'') for n in re.findall("'"+escaped+r"(\\w+)' does not depend on any axioms",output)]
 assert len(reports)==len(names) and {n for n,_ in reports}==set(names),(module,reports,names)
 for name,used in reports:
  assert set(re.findall(r'[\\w.]+',used)) <= {'propext','Classical.choice','Quot.sound'},(module,name,used)
  assert prefix+name+' ' in output,'full type missing'
 result={'audits':len(names),'full_types_checked':True,'axioms':{n:re.findall(r'[\\w.]+',u) for n,u in reports},'original_source_sha256':manifest['sources'][module]['sha256'],'candidate_sha256':hashlib.sha256(raw).hexdigest(),'full_transfer':'OPEN'}
 (leaf/'audit.json').write_text(json.dumps(result,indent=2)+'\\n');total+=len(names)
print(json.dumps({'audits':total,'new_bridge_audits':6,'unchanged_prerequisite_replay_audits':total-6,'full_transfer':'OPEN'}))
'''
ast.parse(audit)
auditor.write_bytes(audit.encode())

old = root / 'root-source-graph-evaluation-current-project-3228.ps1'
body = old.read_text()
old_scope = load(root / 'source-graph-evaluation-current-project-source-3228/manifest.json')['scope']
for before, after in [('source-graph-evaluation-current-project-source-3228', out.name),
                      ('source-graph-evaluation-current-project-kernel-3228', stem + '-kernel'),
                      ('audit-source-graph-evaluation-current-project-3228.py', auditor.name),
                      (old_scope, scope)]:
    assert before in body
    body = body.replace(before, after)
needle = '''if((Get-FileHash -LiteralPath "$taskSource/SourceGraphEvaluation-audited.lean").Hash.ToLowerInvariant() -ne $taskManifest.audited_candidate_sha256){throw 'exact appended type checks required'}'''
assert needle in body
body = body.replace(needle, '''foreach($taskName in $taskManifest.order){
 if((Get-FileHash -LiteralPath "$taskSource/$taskName-audited.lean").Hash.ToLowerInvariant() -ne $taskManifest.audited_candidates.$taskName){throw 'exact type/axiom audited candidate required'}
}''')
needle = '''$taskCandidate=if($taskName -eq 'SourceGraphEvaluation'){"$taskSource/$taskName-audited.lean"}else{"$taskSource/$taskName.lean"}'''
assert needle in body
body = body.replace(needle, '''$taskCandidate="$taskSource/$taskName-audited.lean"''').replace('2048', '1536')
controller = root / ('root-' + stem + '.ps1')
assert not controller.exists()
controller.write_bytes(body.encode())
print(json.dumps({'source_manifest_sha256': sha(out / 'manifest.json'),
                  'controller_sha256': sha(controller), 'auditor_sha256': sha(auditor),
                  'qualified_imports': len(reused), 'fresh_named_modules': fresh,
                  'expected_audits': {k: len(v) for k, v in expected.items()}, 'kernel_run': False}))



