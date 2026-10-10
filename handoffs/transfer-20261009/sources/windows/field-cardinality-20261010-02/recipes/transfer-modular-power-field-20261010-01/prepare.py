"""Three small handwritten modular-power soundness/residue modules."""
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-torsion-euler-20261010-03'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
plan = json.loads((PRIOR / 'plan.json').read_text())
events = [json.loads(x) for x in (PRIOR / 'events.jsonl').read_text().splitlines()]
done = [e for e in events if e['event'] == 'attempt_finished']
assert len(done) == 1 and done[0]['result']['status'] == 'passed'
inventory = DIAG / 'transfer-external-floor-complete-20261010-04/external-floor.json'
assert json.loads(inventory.read_text())['admission_ready']
project = ROOT / 'project/ShielddSecurity'; project.mkdir(parents=True, exist_ok=False)
originals = plan['owned_imports'] + done[0]['result']['objects']; base = []
for p in originals:
    assert pin(p['path']) == p
    dest = project / Path(p['path']).name; shutil.copyfile(p['path'], dest); base.append(pin(dest))
modular = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity/ModularPower.lean')
original = modular.read_text()
names = re.findall(r'^(?:def|theorem)\s+([A-Za-z0-9_.]+)', original, re.M)
assert names == ['power', 'power_lt', 'power_sound', 'power_eq_one', 'power_ne_one']
original += '\n' + '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.ModularPower.' + n + '\n#print axioms ShielddSecurity.ModularPower.' + n for n in names) + '\n'
modular_copy = ROOT / 'handwritten/ModularPower.lean'
modular_copy.write_text(original, encoding='utf-8', newline='\n')
targets = []
for name in ['ModularPower', 'NatModularPowerFieldSound01', 'TorsionEulerResidue01']:
    source = ROOT / 'handwritten' / (name + '.lean')
    dest = project / source.name; shutil.copyfile(source, dest)
    text = dest.read_text(); audits = re.findall(r'^#print axioms ([A-Za-z0-9_.]+)', text, re.M)
    assert re.findall(r'^#check @([A-Za-z0-9_.]+)', text, re.M) == audits
    targets.append({'module': name, 'source': pin(dest), 'predecessor_source': pin(source),
        'imports': re.findall(r'^import\s+([A-Za-z0-9_.]+)', text, re.M), 'audit_names': audits})
runner = ROOT / 'execute_bounded.py'; text = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(text)
runner.write_text(text, encoding='utf-8', newline='\n')
plan['targets'] = targets; plan['owned_imports'] = base; plan['lean_path'][0] = str(ROOT / 'project')
plan['external_floor'] = {**pin(inventory), 'admission_ready': True}
plan['pins'] += [pin(runner), pin(Path(__file__)), pin(inventory), pin(modular), pin(PRIOR / 'plan.json'), pin(PRIOR / 'events.jsonl'), done[0]['result']['stdout']] + originals + base + [t['predecessor_source'] for t in targets]
plan['kind'] = 'KERNEL_INTEGER_TO_ZMOD_RESIDUE_SOUNDNESS'
plan['scope'] = 'Exact existing ModularPower handwritten proofs, binary-recurrence equality, and three actual ZMod-modulus power residues. These semiring power identities require no primality or field assumption; certified prime field, Fermat and nonsquare/torsion/cardinality binding remain open.'
plan['repairs'] = 'Only ordered audits added to existing ModularPower. Two new small symbolic recurrence/residue proof modules. Complete owned dependency closure and expanded official external inventory required before launch; fixed finite guards retained.'
(ROOT / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
(ROOT / 'review.json').write_text(json.dumps({'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'scope': plan['scope']}, indent=2) + '\n')
print(json.dumps({'plan': pin(ROOT / 'plan.json'), 'audits': sum(len(t['audit_names']) for t in targets)}))
