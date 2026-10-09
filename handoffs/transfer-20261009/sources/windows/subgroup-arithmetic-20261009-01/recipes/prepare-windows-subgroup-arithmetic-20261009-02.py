from pathlib import Path
import ast, hashlib, json, re

diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
src = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')
stem = 'windows-subgroup-arithmetic-20261009-02'
out = diag / (stem + '-source')
assert not out.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources, order, expected, candidates = {}, [], {}, {}
strip = lambda s: re.sub(r'(?m)^(?:set_option pp\.all true in\r?\n)?#(?:check|print axioms)[^\r\n]*\r?\n', '', s)
def without_comments(body):
    result, depth, index = [], 0, 0
    while index < len(body):
        if body.startswith('/-', index):
            depth += 1; index += 2
        elif depth and body.startswith('-/', index):
            depth -= 1; index += 2
        elif depth:
            index += 1
        elif body.startswith('--', index):
            next_line = body.find('\n', index)
            index = len(body) if next_line < 0 else next_line
        else:
            result.append(body[index]); index += 1
    assert depth == 0
    return ''.join(result)
def visit(name):
    if name in sources:
        return
    p = src / (name + '.lean')
    raw = p.read_bytes()
    body = raw.decode('utf-8-sig')
    imports = re.findall(r'^import\s+([\w.]+)', body, re.M)
    for dep in imports:
        if dep.startswith('ShielddSecurity.'):
            visit(dep.split('.', 1)[1])
    assert not re.search(r'(?m)^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit|native_decide)\b|(?:maxHeartbeats|maxRecDepth)\s+0\b', without_comments(body))
    sources[name] = {'path': str(p), 'sha256': sha(p), 'bytes': len(raw), 'imports': imports}
    order.append(name)
visit('GroupSubgroupGraphArithmetic')
out.mkdir()
for name in order:
    p = src / (name + '.lean')
    (out / p.name).write_bytes(p.read_bytes())
    body = strip(p.read_text(encoding='utf-8-sig'))
    names = re.findall(r'^theorem\s+(\w+)', body, re.M)
    assert names and len(names) == len(set(names)), name
    ends = list(re.finditer(r'(?m)^end\s+([\w.]+)\s*$', without_comments(body)))
    assert ends, name
    marker = ends[-1].start()
    audits = ''.join(f'\nset_option pp.all true in\n#check @{n}\n#print axioms {n}\n' for n in names)
    audited = body[:marker] + audits + body[marker:]
    assert strip(audited).split() == body.split(), name
    candidate = out / (name + '-audited.lean')
    candidate.write_bytes(audited.encode())
    expected[name], candidates[name] = names, sha(candidate)
scope = 'Reusable arithmetic meaning for the7-node curve block,17-node shared-inverse double, and symbolic triple-double recurrence. Source assertion equations derive OnCurve preimage and nativeEight=point; completeness constructs shared inverses from independent curve/nonzero denominator conditions. Exact typed graph matcher, row inclusion, concrete curve/codec/Crypto interpretation and complete Transfer remain OPEN.'
manifest = {'sources': sources, 'order': order, 'dependency_order': order,
    'expected_theorems_by_module': expected, 'audited_candidates': candidates,
    'reused': [], 'frozen_import_receipts': {}, 'proof_bytes_changed': False,
    'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a', 'scope': scope, 'kernel_run': False,
    'original_mac_source_sha256': 'e0954dbe8c380260ff49f2fdb7e852f8058289b84fe522cc0c56f4d20748f642'}
# The original Mac source identity is computed from the frozen published file.
original = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/sources/mac/mac-field-claim-acceptance/TransferFieldClaimAcceptance.lean')
manifest['original_mac_source_sha256'] = sha(original)
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
print(json.dumps({'audits':total,'scoped_root_audits':len(m['expected_theorems_by_module']['GroupSubgroupGraphArithmetic']),'dependency_replay_audits':total-len(m['expected_theorems_by_module']['GroupSubgroupGraphArithmetic']),'full_transfer':'OPEN'}))
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
    'audits': sum(map(len, expected.values())), 'root_audits': len(expected['GroupSubgroupGraphArithmetic']), 'kernel_run': False}))



