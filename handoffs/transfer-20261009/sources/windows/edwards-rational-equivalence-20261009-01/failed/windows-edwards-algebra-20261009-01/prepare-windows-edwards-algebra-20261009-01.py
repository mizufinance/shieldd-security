from pathlib import Path
import ast, hashlib, json, re

diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
src = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')
stem = 'windows-edwards-algebra-20261009-01'
out = diag / (stem + '-source')
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources, order, expected, candidates = {}, [], {}, {}
reused, receipts, sealed_inputs = [], {}, []
published = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')
for namespace in ['windows-field-certificate-tree-20261009-03', 'windows-field-certificate-pilot-20261009-05', 'windows-subgroup-arithmetic-20261009-03']:
    sealed = diag / (namespace + '-kernel')
    assert (sealed / 'complete.txt').exists() and (sealed / 'end.txt').exists()
    assert (sealed / 'exit.txt').read_text().strip() == '0'
    checked = json.loads((sealed / 'manifest.json').read_text(encoding='utf-8-sig'))
    sealed_inputs.append((sealed, checked))
    for key in ['manifest.json', 'recipe.json', 'complete.txt', 'exit.txt', 'end.txt']:
        receipts[str(sealed / key)] = sha(sealed / key)

strip = lambda s: re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n', '', s)
def without_comments(text):
    result, index, depth = [], 0, 0
    while index < len(text):
        if text[index:index+2] == '/-':
            depth += 1; index += 2
        elif depth and text[index:index+2] == '-/':
            depth -= 1; index += 2
        elif not depth and text[index:index+2] == '--':
            end = text.find('\n', index)
            index = len(text) if end == -1 else end
        else:
            if not depth: result.append(text[index])
            elif text[index] == '\n': result.append('\n')
            index += 1
    assert depth == 0
    return ''.join(result)

def visit(name):
    if name in sources:
        return
    if name.startswith('FieldPrimeNode'):
        p = Path('C:/src/shieldd-transfer-handoffs/field-certificate-tree-20261009-01/ShielddSecurity') / (name + '.lean')
    elif name == 'UpstreamLucasPrimality':
        p = Path('C:/src/shieldd-formal/circuits/.lake/packages/mathlib/Mathlib/NumberTheory/LucasPrimality.lean')
    else:
        p = published / (name + '.lean')
        if not p.exists(): p = src / (name + '.lean')
    for sealed, checked in sealed_inputs:
        if name not in checked['sources'] or sha(p) != checked['sources'][name]['sha256']: continue
        audit = sealed / name / 'audit.json'
        assert audit.exists()
        audited_source = sealed / 'project' / checked['sources'][name].get('lean_relative_path', 'ShielddSecurity/' + name + '.lean')
        object_path = audited_source.with_suffix('.olean')
        assert sha(audited_source) == checked['audited_candidates'][name]
        assert object_path.exists()
        item = {'name': name, 'source': str(audited_source), 'source_sha256': sha(audited_source),
                'object': str(object_path), 'object_sha256': sha(object_path),
                'original_source': str(p), 'original_source_sha256': sha(p), 'lean_relative_path': checked['sources'][name].get('lean_relative_path', 'ShielddSecurity/' + name + '.lean')}
        item['sidecars'] = []
        for suffix in ['.olean.private', '.olean.server', '.ir']:
            extra = audited_source.with_suffix(suffix)
            if extra.exists():
                record = {'path': str(extra), 'sha256': sha(extra),
                    'lean_relative_path': str(Path(item['lean_relative_path']).with_suffix(suffix)).replace('\\', '/')}
                item['sidecars'].append(record)
                receipts[str(extra)] = sha(extra)
        if name == 'UpstreamLucasPrimality': assert any(x['path'].endswith('.olean.private') for x in item['sidecars'])
        if item not in reused: reused.append(item)
        receipts[str(audit)] = sha(audit)
        for dependency in checked['sources'][name]['imports']:
            if dependency.startswith('ShielddSecurity.'): visit(dependency.split('.', 1)[1])
            elif dependency == 'Mathlib.NumberTheory.LucasPrimality': visit('UpstreamLucasPrimality')
        return
    raw = p.read_bytes()
    body = raw.decode('utf-8-sig')
    imports = re.findall(r'^import\s+([\w.]+)', body, re.M)
    for dep in imports:
        if dep.startswith('ShielddSecurity.'):
            visit(dep.split('.', 1)[1])
        elif dep == 'Mathlib.NumberTheory.LucasPrimality':
            visit('UpstreamLucasPrimality')
    assert not re.search(r'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b|(?:maxHeartbeats|maxRecDepth)\s+0\b', without_comments(body))
    sources[name] = {'path': str(p), 'sha256': sha(p), 'bytes': len(raw), 'imports': imports, 'lean_relative_path': ('Mathlib/NumberTheory/LucasPrimality.lean' if name == 'UpstreamLucasPrimality' else 'ShielddSecurity/' + name + '.lean')}
    order.append(name)
visit('EdwardsWeierstrassAlgebra01')
assert 'Group' in {item['name'] for item in reused}
out.mkdir()
for name in order:
    p = Path(sources[name]['path'])
    (out / (name + '.lean')).write_bytes(p.read_bytes())
    body = strip(p.read_text(encoding='utf-8-sig'))
    names = re.findall(r'^theorem\s+(\w+)', body, re.M)
    assert len(names) == len(set(names)), name
    assert names or name in ['TransferFirstSubgroupTables01', 'TransferFirstSubgroupTables02', 'CompilerIndexCoverage01'], name
    ends = list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$', body))
    assert ends or name == 'UpstreamLucasPrimality', name
    marker = ends[-1].start() if ends else len(body)
    audits = ''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n' for n in names)
    audited = body[:marker] + audits + body[marker:]
    assert strip(audited).split() == body.split(), name
    candidate = out / (name + '-audited.lean')
    candidate.write_bytes(audited.encode())
    expected[name], candidates[name] = names, sha(candidate)
scope = 'Bounded algebra pilot: exceptional Edwards coordinates, nonzero Montgomery B from explicit parameters, and coordinate negation maps. Full rational-point equivalence, Mathlib point join, addition, cardinality and native representation OPEN.'
manifest = {'sources': sources, 'order': order, 'dependency_order': order,
    'expected_theorems_by_module': expected, 'audited_candidates': candidates,
    'reused': reused, 'frozen_import_receipts': receipts, 'proof_bytes_changed': True, 'parent_commit': 'e90e824285275bd59eac9fb1f5d173b9e38b0d17', 'candidate_sha256': '20d3da8789fc847a4e5450c430321b52350e79f7533bcd43ff48695ffa4c862d',
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'scope': scope, 'kernel_run': False,
    'original_mac_source_sha256': 'e0954dbe8c380260ff49f2fdb7e852f8058289b84fe522cc0c56f4d20748f642'}
manifest.pop('original_mac_source_sha256')
(out / 'manifest.json').write_bytes((json.dumps(manifest, indent=2) + '\n').encode())
audit = '''from pathlib import Path
import hashlib,json,re,sys
batch=Path(sys.argv[1]);m=json.loads((batch/'manifest.json').read_text(encoding='utf-8-sig'));total=0
for module,names in m['expected_theorems_by_module'].items():
 leaf=batch/module;assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
 source=batch/'project'/m['sources'][module]['lean_relative_path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==m['audited_candidates'][module]
 output=(leaf/'stdout.txt').read_text(encoding='utf-8-sig');stderr=(leaf/'stderr.txt').read_text(encoding='utf-8-sig');assert not re.search(r'\\b(sorryAx|error)\\b',output+stderr)
 reports=re.findall(r"'([\\w.]+)' depends on axioms: \\[([^\\]]*)\\]",output)
 reports += [(n,'') for n in re.findall(r"'([\\w.]+)' does not depend on any axioms",output)]
 assert len(reports)==len(names),(module,len(reports),len(names))
 used_names=set()
 for short in names:
  matches=[(full,used) for full,used in reports if full==short or full.endswith('.'+short)]
  assert len(matches)==1,(module,short,matches)
  full,used=matches[0];assert set(re.findall(r'[\\w.]+',used)) <= {'propext','Classical.choice','Quot.sound'},(module,full,used)
  assert re.search(r'(?:^|\\n)@?'+re.escape(full)+r'\\s*:',output),'full type missing'
  used_names.add(full)
 assert len(used_names)==len(names)
 result={'audits':len(names),'full_types_checked':True,'axioms':{n:re.findall(r'[\\w.]+',u) for n,u in reports},'original_source_sha256':m['sources'][module]['sha256'],'candidate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'full_transfer':'OPEN'}
 (leaf/'audit.json').write_text(json.dumps(result,indent=2)+'\\n');total+=len(names)
print(json.dumps({'audits':total,'scoped_root_audits':len(m['expected_theorems_by_module']['EdwardsWeierstrassAlgebra01']),'dependency_replay_audits':total-len(m['expected_theorems_by_module']['EdwardsWeierstrassAlgebra01']),'full_transfer':'OPEN'}))
'''
ast.parse(audit)
auditor = diag / ('audit-' + stem + '.py')
auditor.write_bytes(audit.encode())
old = diag / 'root-windows-graph-input-bridge-20261009-05.ps1'
body = old.read_text()
previous = json.loads((diag / 'windows-graph-input-bridge-20261009-05-source/manifest.json').read_text())['scope']
body = body.replace('windows-graph-input-bridge-20261009-05', stem).replace(previous, scope)
controller = diag / ('root-' + stem + '.ps1')
body=body.replace('  $taskLeaf=', "  $taskRelativeSource=$taskManifest.sources.$taskName.lean_relative_path\n  $taskRelativeObject=$taskRelativeSource.Replace('.lean','.olean')\n  $taskLeaf=")
body=body.replace('$taskStage/ShielddSecurity/$taskName.lean', '$taskStage/$taskRelativeSource')
body=body.replace('$taskStage/ShielddSecurity/$taskName.olean', '$taskStage/$taskRelativeObject')
body=body.replace('  Copy-Item -LiteralPath $taskCandidate', '  New-Item -ItemType Directory -Path (Split-Path -Parent "$taskStage/$taskRelativeSource") -Force|Out-Null\n  Copy-Item -LiteralPath $taskCandidate')
body=body.replace('[DateTime]::UtcNow.ToString(\'o\')|Set-Content "$taskBatch/start.txt"', '$taskComposer=\'C:/src/shieldd-transfer-handoffs/compose-edwards-algebra-cache-20261009-01.py\'\nif((Get-FileHash -LiteralPath $taskComposer).Hash.ToLowerInvariant() -ne \'0b0ff5fd05e0153ca068af982371f24bc25b8f0a118d49eaba4d6d31ec447234\'){throw \'exact diagnostic cache composer required\'}\n& \'C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe\' $taskComposer $taskStage\nif($LASTEXITCODE -ne 0){throw \'complete diagnostic cache composition required\'}\n[DateTime]::UtcNow.ToString(\'o\')|Set-Content "$taskBatch/start.txt"')
body=body.replace('$taskStage/ShielddSecurity/$($taskImport.name).lean', '$taskStage/$($taskImport.lean_relative_path)')
body=body.replace('$taskStage/ShielddSecurity/$($taskImport.name).olean', "$taskStage/$($taskImport.lean_relative_path.Replace('.lean','.olean'))")
body=body.replace(' Copy-Item -LiteralPath $taskImport.object -Destination "$taskStage/$($taskImport.lean_relative_path.Replace(\'.lean\',\'.olean\'))"', ' Copy-Item -LiteralPath $taskImport.object -Destination "$taskStage/$($taskImport.lean_relative_path.Replace(\'.lean\',\'.olean\'))"\n foreach($taskExtra in $taskImport.sidecars){\n  if((Get-FileHash -LiteralPath $taskExtra.path).Hash.ToLowerInvariant() -ne $taskExtra.sha256){throw \'qualified companion changed\'}\n  Copy-Item -LiteralPath $taskExtra.path -Destination "$taskStage/$($taskExtra.lean_relative_path)"\n }\n')
body=body.replace(' foreach($taskDep in $taskDeps)', ' foreach($taskImport in $taskManifest.reused){foreach($taskExtra in $taskImport.sidecars){\n if((Get-FileHash -LiteralPath "$taskStage/$($taskExtra.lean_relative_path)").Hash.ToLowerInvariant() -ne $taskExtra.sha256){throw \'copied qualified companion changed\'}\n }}\n foreach($taskDep in $taskDeps)')
controller.write_bytes(body.encode())
print(json.dumps({'modules': len(order), 'source_manifest_sha256': sha(out/'manifest.json'),
    'controller_sha256': sha(controller), 'auditor_sha256': sha(auditor),
    'audits': sum(map(len, expected.values())), 'root_audits': len(expected['EdwardsWeierstrassAlgebra01']), 'kernel_run': False}))


