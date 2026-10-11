"""Explicit declaration census independent of diagnostic ordering."""
import json
import re
from pathlib import Path

J = Path(__file__).resolve().parent
packets = [J / 'audit-result01.json'] + sorted(J.glob('*-audit01.json'))
rows = []
seen = set()
for path in packets:
    for module in json.loads(path.read_bytes())['modules']:
        name = module['module']
        assert name not in seen
        seen.add(name)
        text = Path(module['source']['path']).read_text()
        text = re.sub(r'/-.*?-/', '', text, flags=re.S)
        text = re.sub(r'--[^\n]*', '', text)
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe)\b', text)
        namespace = re.findall(r'(?m)^namespace ([\w.]+)\s*$', text)
        assert namespace == ['ShielddSecurity.' + name]
        names = []
        for match in re.finditer(r'(?m)^(?P<mods>(?:(?:noncomputable|private|protected)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class)\s+(?P<name>[\w.]+)', text):
            if 'private' not in match['mods'].split():
                names.append(namespace[0] + '.' + match['name'])
        reported = [a['name'] for a in module['audits']]
        assert len(names) == len(set(names)) and sorted(names) == sorted(reported), name
        rows.append({'module': name, 'source': module['source'],
                     'lexical_declarations': names, 'diagnostic_declarations': reported})
result = {'kind': 'Independent explicit public declaration inventory for sealed arithmetic support; full import/publication review pending',
          'modules': rows, 'declarations': sum(len(r['lexical_declarations']) for r in rows),
          'kernel_replay': False, 'full_transfer': 'OPEN'}
(J / 'declaration-inventory01.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'modules': len(rows), 'declarations': result['declarations']}))
