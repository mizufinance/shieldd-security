"""Audit framing successor of immutable SOURCE47; no proof-body edits, compiler or caches."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
PACKET = ROOT.parent / 'transfer-group-source47-20261010-01' / 'inputs' / 'packet'
MAIN = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')
def pin(p):
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
manifest = json.loads((PACKET / 'portable-source-manifest01.json').read_text())
expected = {Path(r['path']).stem: r for r in manifest['files'] if r['path'].endswith('.lean')}
order = ['Group', 'GroupWindows', 'GroupExtended', 'GroupRowCompletion', 'CompilerLinearCompletion',
         'GroupCircuitCompletion', 'GroupCircuitOrder', 'CompilerIndexed01']
project = ROOT / 'project' / 'ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
targets = []
def body(text):
    lines = [line for line in text.splitlines() if not re.match(r'^(?:#check\b|#print axioms\b|set_option pp\.all true in\s*$|-- GENERATED SOURCE-only)', line)]
    return '\n'.join(lines).strip() + '\n'
for name in order:
    source = PACKET / expected[name]['path'] if name in expected else MAIN / (name + '.lean')
    p = pin(source)
    if name in expected:
        assert (p['bytes'], p['sha256']) == (expected[name]['bytes'], expected[name]['sha256'])
    else:
        assert p['sha256'] == {'CompilerLinearCompletion': '40180a373e7ad6e523b57158c048b8816fdef28c21146ecc21795a952453da64',
          'CompilerIndexed01': 'df0052860d8930e845df81057af9693cc50e06a1fba547d8420f532f14cab185'}[name]
    original = source.read_text()
    text = body(original)
    assert [int(n) for n in re.findall(r'set_option maxHeartbeats\s+(\d+)', text)] == [300000]
    scope, = re.findall(r'^namespace ([A-Za-z0-9_.]+)$', text, re.M)
    names = [scope + '.' + n for n in re.findall(r'^(?:def|noncomputable def|theorem|structure|inductive) ([A-Za-z0-9_.]+)', text, re.M)]
    assert len(names) == len(set(names))
    if 'set_option maxRecDepth' not in text:
        text = text.replace('set_option maxHeartbeats 300000', 'set_option maxHeartbeats 300000\nset_option maxRecDepth 4096', 1)
    assert re.findall(r'set_option maxRecDepth\s+(\d+)', text) == ['4096']
    for full in names:
        text += '\nset_option pp.all true in\n#check @' + full + '\n#print axioms ' + full + '\n'
    header = '-- GENERATED SOURCE-only by generate_successors.py; fresh audits UNRUN.\n'
    dest = project / (name + '.lean')
    dest.write_text(header + text, encoding='utf-8', newline='\n')
    original_body = body(original)
    actual_body = body(dest.read_text())
    if 'set_option maxRecDepth' not in original_body:
        actual_body = actual_body.replace('set_option maxRecDepth 4096\n', '', 1)
    assert actual_body == original_body
    targets.append({'module': name, 'source': pin(dest), 'predecessor_source': p,
        'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': names,
        'proof_body_comparison': 'Exact after removing audit framing, generated header and newly inserted finite recursion setting.'})
out = {'kind': 'SOURCE_ONLY_AUDIT_FRAMING_SUCCESSOR', 'recipe': pin(Path(__file__)),
       'packet_manifest': pin(PACKET / 'portable-source-manifest01.json'), 'targets': targets,
       'kernel_status': 'UNRUN', 'credit': 0}
(ROOT / 'source-manifest.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'modules': [{'module': t['module'], 'audits': len(t['audit_names']), 'bytes': t['source']['bytes']} for t in targets],
 'body_comparisons': 'all exact', 'kernel_status': 'UNRUN'}))
