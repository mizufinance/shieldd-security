from pathlib import Path
import ast, hashlib, json, re

diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
src = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')
stem = 'windows-connected-subgroup-semantics-20261009-01'
out = diag / (stem + '-source')
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources, order, expected, candidates = {}, [], {}, {}
reused, receipts, sealed_inputs = [], {}, []
published = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/sources/mac/mac-connected-subgroup01/final01/project/ShielddSecurity')
for namespace in ['windows-subgroup-source-graph-20261009-05', 'windows-subgroup-arithmetic-20261009-03']:
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
    p = published / (name + '.lean')
    if not p.exists(): p = src / (name + '.lean')
    for sealed, checked in sealed_inputs:
        if name not in checked['sources'] or sha(p) != checked['sources'][name]['sha256']: continue
        audit = sealed / name / 'audit.json'
        assert audit.exists()
        audited_source = sealed / 'project/ShielddSecurity' / (name + '.lean')
        object_path = audited_source.with_suffix('.olean')
        assert sha(audited_source) == checked['audited_candidates'][name]
        assert object_path.exists()
        item = {'name': name, 'source': str(audited_source), 'source_sha256': sha(audited_source),
                'object': str(object_path), 'object_sha256': sha(object_path),
                'original_source': str(p), 'original_source_sha256': sha(p)}
        if item not in reused: reused.append(item)
        receipts[str(audit)] = sha(audit)
        for dependency in checked['sources'][name]['imports']:
            if dependency.startswith('ShielddSecurity.'): visit(dependency.split('.', 1)[1])
        return
    raw = p.read_bytes()
    body = raw.decode('utf-8-sig')
    imports = re.findall(r'^import\s+([\w.]+)', body, re.M)
    for dep in imports:
        if dep.startswith('ShielddSecurity.'):
            visit(dep.split('.', 1)[1])
    assert not re.search(r'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b|(?:maxHeartbeats|maxRecDepth)\s+0\b', without_comments(body))
    sources[name] = {'path': str(p), 'sha256': sha(p), 'bytes': len(raw), 'imports': imports}
    order.append(name)
visit('TransferFirstSubgroupSemantics01')
out.mkdir()
for name in order:
    p = Path(sources[name]['path'])
    (out / p.name).write_bytes(p.read_bytes())
    body = strip(p.read_text(encoding='utf-8-sig'))
    names = re.findall(r'^theorem\s+(\w+)', body, re.M)
    assert len(names) == len(set(names)), name
    assert names or name in ['TransferFirstSubgroupTables01', 'TransferFirstSubgroupTables02'], name
    ends = list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$', body))
    assert ends, name
    marker = ends[-1].start()
    audits = ''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n' for n in names)
    audited = body[:marker] + audits + body[marker:]
    assert strip(audited).split() == body.split(), name
    candidate = out / (name + '-audited.lean')
    candidate.write_bytes(audited.encode())
    expected[name], candidates[name] = names, sha(candidate)
scope = 'Concrete first registry dk: exact published SourceGraph 22735 80 syntax match, all six independent source assertions, actual71 original-row arbitrary-assignment soundness, and native constructor satisfying those rows while preserving22735 inputs. Independent subgroup admission constructs SDK preimage and shared inverse hints; identity permitted. Two/four nonzero derived from characteristic. Named curve/codec/Crypto deployment, other full Transfer graph blocks and native/state refinement remain OPEN.'
manifest = {'sources': sources, 'order': order, 'dependency_order': order,
    'expected_theorems_by_module': expected, 'audited_candidates': candidates,
    'reused': reused, 'frozen_import_receipts': receipts, 'proof_bytes_changed': False,
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'scope': scope, 'kernel_run': False,
    'original_mac_source_sha256': 'e0954dbe8c380260ff49f2fdb7e852f8058289b84fe522cc0c56f4d20748f642'}
manifest.pop('original_mac_source_sha256')
(out / 'manifest.json').write_bytes((json.dumps(manifest, indent=2) + '\n').encode())
audit = '''from pathlib import Path
import hashlib,json,re,sys
batch=Path(sys.argv[1]);m=json.loads((batch/'manifest.json').read_text(encoding='utf-8-sig'));total=0
for module,names in m['expected_theorems_by_module'].items():
 leaf=batch/module;assert (leaf/'end.txt').exists() and (leaf/'exit.txt').read_text().strip()=='0' and not (leaf/'stop.txt').exists()
 source=batch/'project/ShielddSecurity'/(module+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==m['audited_candidates'][module]
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
print(json.dumps({'audits':total,'scoped_root_audits':len(m['expected_theorems_by_module']['TransferFirstSubgroupSemantics01']),'dependency_replay_audits':total-len(m['expected_theorems_by_module']['TransferFirstSubgroupSemantics01']),'full_transfer':'OPEN'}))
'''
ast.parse(audit)
auditor = diag / ('audit-' + stem + '.py')
auditor.write_bytes(audit.encode())
old = diag / 'root-windows-graph-input-bridge-20261009-05.ps1'
body = old.read_text()
previous = json.loads((diag / 'windows-graph-input-bridge-20261009-05-source/manifest.json').read_text())['scope']
body = body.replace('windows-graph-input-bridge-20261009-05', stem).replace(previous, scope)
controller = diag / ('root-' + stem + '.ps1')
controller.write_bytes(body.encode())
print(json.dumps({'modules': len(order), 'source_manifest_sha256': sha(out/'manifest.json'),
    'controller_sha256': sha(controller), 'auditor_sha256': sha(auditor),
    'audits': sum(map(len, expected.values())), 'root_audits': len(expected['TransferFirstSubgroupSemantics01']), 'kernel_run': False}))


