"""Preserve and qualify two handwritten prerequisites; no runtime edits."""
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
for module, names in [
    ('GroupNativeSdk', ['FqBytes', 'FrBytes', 'Sdk', 'readFq', 'readScalar', 'admissionGate',
                       'fq_read', 'scalar_read', 'scalar_canonical', 'native_point_read',
                       'admission', 'admitted_key', 'generator_embedding', 'randomize_embedding',
                       'randomized_admission', 'randomized_native_authorization']),
    ('ShielddScalarReader', ['Backend', 'ReadCfg', 'readCfg', 'decoder',
                            'allow_zero_canonical', 'decoder_canonical', 'reject_zero_exact'])]:
    source = MAIN / (module + '.lean')
    text = source.read_text()
    text = re.sub(r'^set_option pp\.all true in\n#check @[^\n]+\n#print axioms [^\n]+\n?', '', text, flags=re.M)
    text = text.replace('set_option maxHeartbeats 400000', 'set_option maxHeartbeats 300000')
    text = text.replace('set_option maxHeartbeats 300000',
                        'set_option maxHeartbeats 300000\nset_option maxRecDepth 4096', 1)
    for name in names:
        full = 'ShielddSecurity.' + module + '.' + name
        text += '\nset_option pp.all true in\n#check @' + full + '\n#print axioms ' + full + '\n'
    target = ROOT / 'handwritten' / source.name
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    target.write_text(text, encoding='utf-8', newline='\n')
    records.append({'module': module, 'prior_handwritten': pin(source), 'candidate': pin(target),
                    'audit_names': ['ShielddSecurity.' + module + '.' + name for name in names],
                    'changes': 'Full qualified type/axiom inventory; finite maxRecDepth4096 and heartbeat cap300000. Existing proof bodies and contracts preserved.'})
(ROOT / 'source-review.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'sources': 2, 'audits': 23, 'pins': records}))
