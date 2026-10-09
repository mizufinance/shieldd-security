"""Check that all 51 logged prime conclusions have no residual premise."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STAGE = ROOT / 'work/mac-subgroup-prime06'
OUTPUT = ROOT / 'outputs/mac-subgroup-prime06'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__:
        raise RuntimeError('optimized Python forbidden')
    candidate = STAGE / 'candidate.json'
    assert digest(candidate) == '905fb641efe1b86350c7d5a801741cdee2d368401c58712c751f8de5781d5150'
    data = json.loads(candidate.read_text())
    inherited = json.loads((STAGE / 'inherited-prime-map01.json').read_text())['primes']
    names = {int(number): module for number, module in inherited.items()}
    new = sorted(int(number) for number in data['certificates'] if int(number) not in names)
    assert len(names) == 14 and len(new) == 37
    names.update({number: f'SubgroupPrimeNode{index + 1:02d}'
                  for index, number in enumerate(new)})
    results = []
    for number, module in sorted(names.items()):
        owner = 'SubgroupPrimeInheritedAudit06' if str(number) in inherited else module
        matches = []
        for receipt in OUTPUT.glob(f'build-{owner}-*.json'):
            report = json.loads(receipt.read_text())
            if report['status'] == 'passed':
                matches.append((receipt, report))
        assert len(matches) == 1, (module, 'ambiguous passing receipt')
        receipt, report = matches[0]
        log = receipt.with_suffix('.log')
        assert report['exit'] == 0 and digest(log) == report['log_sha256']
        owner_source = STAGE / 'project/ShielddSecurity' / f'{owner}.lean'
        assert digest(owner_source) == report['source_sha256']
        full_name = f'ShielddSecurity.{module}.prime'
        text = log.read_text()
        found = re.findall(r'^' + re.escape(full_name) +
            r'\s*:[\s\S]*?(?=^\'' + re.escape(full_name) + r'\')', text, re.M)
        assert len(found) == 1, full_name
        expected = (f'{full_name} : Nat.Prime (@OfNat.ofNat.{{0}} Nat '
            f'(nat_lit {number}) (instOfNatNat (nat_lit {number})))')
        assert ' '.join(found[0].split()) == expected, (full_name, found)
        audits = re.findall(r"'" + re.escape(full_name) +
            r"' depends on axioms: \[([^]]*)\]", text)
        assert len(audits) == 1
        assert set(part.strip() for part in audits[0].split(',')) <= {
            'propext', 'Classical.choice', 'Quot.sound'}
        results.append(dict(number=number, theorem=full_name,
            receipt=str(receipt.relative_to(ROOT)), receipt_sha256=digest(receipt),
            log_sha256=digest(log), exact_no_premise_numeric_type=True))
    result = dict(kind='parent-exact-51-numeric-conclusion-review',
        candidate_sha256=digest(candidate), results=results,
        root=data['subgroup_order'], new_kernel_run=False, full_transfer='OPEN')
    (HERE / 'prime-types-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: 51 exact numeric prime conclusions, with only standard axioms')

if __name__ == '__main__':
    main()
