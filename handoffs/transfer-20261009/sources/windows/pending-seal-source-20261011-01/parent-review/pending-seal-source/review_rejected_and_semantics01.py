"""Review complete retained failures and exact source contracts; no builds."""
from pathlib import Path
import difflib, hashlib, json, re

D = Path(__file__).parent
P = D / 'packet01'
module = 'TransferPendingSealSource01'
current = (P / 'source/ShielddSecurity' / (module + '.lean')).read_text()
def declarations(s):
    result = {}
    pattern = r'(?m)^(?P<kind>inductive|def|theorem) (?P<name>\w+)\b[\s\S]*?(?=^(?:inductive|def|theorem|set_option pp.all|end) |\Z)'
    for m in re.finditer(pattern, s):
        text = m.group(0).strip()
        if m['kind'] == 'theorem':
            assert ' := by' in text
            text = text.split(' := by', 1)[0]
        result[m['name']] = (m['kind'], text)
    return result
now = declarations(current)
assert len(now) == 13 and sum(k == 'theorem' for k, _ in now.values()) == 9
rejected = []
for directory in ['rejected-01', 'rejected-02']:
    R = P / directory
    old = (R / 'handwritten' / (module + '.lean')).read_text()
    assert (R / 'project/ShielddSecurity' / (module + '.lean')).read_text() == old
    normalized = re.sub(r'\bseal\b', 'sealOnce', old) if directory == 'rejected-01' else old
    assert declarations(normalized) == now
    events = [json.loads(line) for line in (R / 'events.jsonl').read_text().splitlines()]
    assert len(events) == 2
    result = events[-1]['result']
    assert result['status'] == 'failed'
    assert result['reason'] == 'Lean exit 1'
    stdout = (R / 'runs' / ('01-' + module) / 'stdout.txt').read_bytes()
    manifest = json.loads((P / 'manifest.json').read_bytes())
    relative = directory + '/runs/01-' + module + '/stdout.txt'
    pins = [e['original'] for e in manifest['entries'] if e['archive_path'] == relative]
    assert len(pins) == 1
    assert len(stdout) == pins[0]['bytes'] and hashlib.sha256(stdout).hexdigest() == pins[0]['sha256']
    assert (R / 'execute_bounded.py').read_bytes() == (P / 'qualified/execute_bounded.py').read_bytes()
    diagnostics = [line for line in stdout.decode().splitlines() if 'error:' in line]
    assert diagnostics
    rejected.append({'directory': directory, 'result': result, 'diagnostics': diagnostics,
                     'contracts_equal_after_helper_rename': True,
                     'normalization': 'Reserved helper seal renamed sealOnce' if directory == 'rejected-01' else 'None; proof-only frame rewrite',
                     'exact_delta': ''.join(difflib.unified_diff(old.splitlines(True), current.splitlines(True))),
                     'scope': 'Entire failed elaboration is not a proof result or a semantic negative control'})
for directory in ['unexecuted-sealer-01', 'unexecuted-sealer-02']:
    assert not list((P / directory).rglob('events.jsonl'))
report = {'status': 'PASSED', 'kind': 'Independent source contract, retained failure and pinned Rust branch review',
          'rejected': rejected, 'unexecuted_packaging_attempts': ['unexecuted-sealer-01', 'unexecuted-sealer-02'],
          'source_review': ['freeze replaces membership by ordered.contains, matching the Sealed enum branch.',
                            'sealOnce reads the current child object with absence defaulting to Open empty; the only success update is its object key.',
                            'ensureSealed treats actual object absence as success and rejects present decoded Open.',
                            'Repeat seal derives its failure from the freshly stored object under the explicit encoding roundtrip.',
                            'Whole later-staging refusal uses Request.nonempty and derives the contradiction from inspection success requiring Open; it does not assume desired body failure.',
                            'Returned failure preserves enclosing parent/queue. Native enum/typed/ownership/codec/Host/persistence/NOMT correspondence is still explicit or open.'],
          'rust_review': str(D.parent / 'pending-seal-rust-source-review01.json'),
          'mathematical_findings': [], 'full_transfer': 'OPEN'}
with (D / 'rejected-and-semantic-review01.json').open('x') as f:
    json.dump(report, f, indent=2)
    f.write('\n')
print(json.dumps({'status': report['status'], 'rejected': len(rejected), 'public_contracts': len(now)}))
