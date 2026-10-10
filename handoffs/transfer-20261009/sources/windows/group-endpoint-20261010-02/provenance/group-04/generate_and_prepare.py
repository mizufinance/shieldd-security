"""Fresh finite task; repair the generator recipe, never its sealed outputs."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
CONFIG = json.loads((ROOT / 'repairs.json').read_text())
OLD = ROOT.parent / CONFIG['predecessor']
ORIGINAL = ROOT.parent / 'transfer-group-source47-20261010-02' / 'source-manifest.json'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
def body(text):
    return '\n'.join(line for line in text.splitlines() if not re.match(
        r'^(?:#check\b|#print axioms\b|set_option pp\.all true in\s*$|-- GENERATED SOURCE-only)', line)).strip() + '\n'
def code_only(text):
    """Mask nested Lean comments and string contents, retaining line structure."""
    output = []
    i = 0
    depth = 0
    string = False
    line_comment = False
    while i < len(text):
        pair = text[i:i+2]
        char = text[i]
        if line_comment:
            output.append('\n' if char == '\n' else ' ')
            if char == '\n': line_comment = False
            i += 1
        elif depth:
            if pair == '/-': depth += 1; output.extend('  '); i += 2
            elif pair == '-/': depth -= 1; output.extend('  '); i += 2
            else: output.append('\n' if char == '\n' else ' '); i += 1
        elif string:
            if char == '\\' and i + 1 < len(text): output.extend('  '); i += 2
            else:
                if char == '"': string = False
                output.append('\n' if char == '\n' else ' '); i += 1
        elif pair == '--': line_comment = True; output.extend('  '); i += 2
        elif pair == '/-': depth = 1; output.extend('  '); i += 2
        elif char == '"': string = True; output.append(' '); i += 1
        else: output.append(char); i += 1
    assert not depth and not string
    return ''.join(output)
assert re.findall(r'^(?:def|theorem|inductive) (\w+)', code_only('/- outer\ninductive fake\n/- nested -/ -/\ntheorem real : True := by trivial\n'), re.M) == ['real']
plan = json.loads((OLD / 'plan.json').read_text())
events = [json.loads(line) for line in (OLD / 'events.jsonl').read_text().splitlines()]
finished = [e for e in events if e['event'] == 'attempt_finished']
assert len(finished) == len([e for e in events if e['event'] == 'attempt_started'])
passed = [e for e in finished if e['result']['status'] == 'passed']
assert [e['module'] for e in passed] == CONFIG['expected_passes']
assert finished[-1]['module'] == CONFIG['failed_module'] and finished[-1]['result']['status'] == 'failed'
project = ROOT / 'project' / 'ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
old_base = plan['owned_imports'] + [obj for e in passed for obj in e['result']['objects']]
base = []
for obj in old_base:
    assert pin(obj['path']) == obj
    dest = project / Path(obj['path']).name
    shutil.copyfile(obj['path'], dest)
    base.append(pin(dest))
originals = {t['module']: t for t in json.loads(ORIGINAL.read_text())['targets']}
targets = []
for previous in plan['targets'][len(passed):]:
    name = previous['module']
    original = originals[name]['predecessor_source']
    assert pin(original['path']) == original
    text = body(Path(original['path']).read_text())
    code = code_only(text)
    scope, = re.findall(r'^namespace ([A-Za-z0-9_.]+)$', code, re.M)
    names = [scope + '.' + n for n in re.findall(r'^(?:def|noncomputable def|theorem|structure|inductive) ([A-Za-z0-9_.]+)', code, re.M)]
    assert set(names) <= set(originals[name]['audit_names'])
    for before, after, count in CONFIG['repairs'].get(name, []):
        assert text.count(before) == count
        text = text.replace(before, after)
    expected_body = text
    if 'set_option maxRecDepth' not in text:
        text = text.replace('set_option maxHeartbeats 300000', 'set_option maxHeartbeats 300000\nset_option maxRecDepth 4096', 1)
    assert re.findall(r'set_option maxHeartbeats\s+(\d+)', text) == ['300000']
    assert re.findall(r'set_option maxRecDepth\s+(\d+)', text) == ['4096']
    for full in names:
        text += '\nset_option pp.all true in\n#check @' + full + '\n#print axioms ' + full + '\n'
    dest = project / (name + '.lean')
    dest.write_text('-- GENERATED SOURCE-only by generate_and_prepare.py; fresh audits UNRUN.\n' + text, encoding='utf-8', newline='\n')
    actual_body = body(dest.read_text())
    if 'set_option maxRecDepth' not in expected_body:
        actual_body = actual_body.replace('set_option maxRecDepth 4096\n', '', 1)
    assert actual_body == expected_body
    targets.append({'module': name, 'source': pin(dest), 'predecessor_source': original,
        'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', code, re.M), 'audit_names': names,
        'proof_body_comparison': 'Exact modulo finite recursion option and explicitly listed generator repairs.'})
manifest = {'kind': 'GENERATED_SOURCE_ONLY_REPAIR', 'recipe': pin(Path(__file__)), 'config': pin(ROOT / 'repairs.json'),
    'generator_correction': 'Comments and strings masked before declaration/import extraction. Phantom Group.invariant came from prose; removed. No mathematical body change.',
    'original_manifest': pin(ORIGINAL), 'targets': targets, 'repairs': CONFIG['repairs'], 'kernel_status': 'UNRUN'}
(ROOT / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
runner = ROOT / 'execute_bounded.py'
text = (OLD / 'execute_bounded.py').read_text()
ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['targets'] = targets
plan['lean_path'][0] = str(ROOT / 'project')
plan['owned_imports'] = base
plan['pins'] += [pin(runner), pin(OLD / 'plan.json'), pin(OLD / 'events.jsonl'), pin(Path(__file__)),
    pin(ROOT / 'repairs.json'), pin(ROOT / 'source-manifest.json'), pin(ORIGINAL)]
plan['pins'] += old_base + base + [t['predecessor_source'] for t in targets]
plan['pins'] += [e['result']['stdout'] for e in passed]
plan['predecessor'] = {'events': pin(OLD / 'events.jsonl'), 'failed_module': CONFIG['failed_module'],
    'attempts': len(finished), 'reason': CONFIG['reason']}
plan['repairs'] = CONFIG['repairs']
plan['status'] = 'FROZEN_SELF_REVIEWED_UNRUN'
plan['artifact_policy'] = 'Only qualified base objects copied and counted; no failed object imported; new generator outputs sealed.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'base_count': len(base),
    'targets': [{'module': t['module'], 'audits': len(t['audit_names'])} for t in targets], 'repairs': CONFIG['repairs'],
    'guards': 'Unchanged finite limits, Windows job, mutex, pressure, import/cache, output and strict audit guards.',
    'retained_bytes': sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review, indent=2))
