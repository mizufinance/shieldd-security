"""Preserve exact owned SDK, scalar and preimage bodies, audit all public declarations."""
import hashlib
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
MAIN = Path('C:/src/shieldd-formal/circuits/ShielddSecurity')

def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

records = []
for module in ['ShielddNativeSdk', 'ShielddNativeScalar', 'GroupNativeSdkPreimage']:
    source = MAIN / (module + '.lean')
    text = source.read_text()
    text = re.sub(r'^set_option pp\.all true in\n#check @[^\n]+\n#print axioms [^\n]+\n?', '', text, flags=re.M)
    text = text.replace('set_option maxHeartbeats 400000', 'set_option maxHeartbeats 300000')
    text = text.replace('set_option maxHeartbeats 300000',
                        'set_option maxHeartbeats 300000\nset_option maxRecDepth 4096', 1)
    names = re.findall(r'^(?:noncomputable )?(?:structure|inductive|def|theorem|lemma|abbrev) ([A-Za-z0-9_]+)', text, re.M)
    for name in names:
        full = 'ShielddSecurity.' + module + '.' + name
        text += '\nset_option pp.all true in\n#check @' + full + '\n#print axioms ' + full + '\n'
    target = ROOT / 'handwritten' / source.name
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    target.write_text(text, encoding='utf-8', newline='\n')
    records.append({'module': module, 'prior_handwritten': pin(source), 'candidate': pin(target),
                    'audit_names': ['ShielddSecurity.' + module + '.' + name for name in names],
                    'changes': 'All public declarations have full type/axiom audits; finite options300000/4096. Existing owned bodies and global primitive contracts preserved.'})
(ROOT / 'source-review.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'sources': len(records), 'audits': sum(len(r['audit_names']) for r in records),
                  'modules': [{'module': r['module'], 'audits': len(r['audit_names']), 'candidate': r['candidate']} for r in records]}))
