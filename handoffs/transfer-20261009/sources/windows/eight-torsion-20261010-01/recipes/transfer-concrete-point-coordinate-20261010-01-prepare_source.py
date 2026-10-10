"""Adapt the published handwritten row bridge to the newly certified actual field."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PUB = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')
source = (PUB / 'ConcretePointOperationRows01.lean').read_text()
source = source.replace('import ShielddSecurity.ConcreteWeierstrassPoint01',
    'import ShielddSecurity.ConcretePointDoublingSquare01')
source = source.replace('ConcretePointOperationRows01', 'ConcretePointCoordinateRows01')
source = source.replace('open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01\nvariable [DecidableEq F]',
    'open TorsionCertifiedField01 ConcretePointTorsion01')
integer = (PUB / 'ConcreteIntegerCertificates01.lean').read_text()
integer = integer[integer.index('/-- A kernel-checked'):integer.index('end ShielddSecurity.ConcreteIntegerCertificates01')]
integer = integer.replace('Scalar.modulus', 'TorsionEulerInteger49.modulus')
marker = '/-- Input equations and a nonvertical branch'
assert source.count(marker) == 1
source = source.replace(marker, integer + '\n' + marker)
names = ['field_eq', 'field_nonzero', 'add_coordinates', 'secant_rows', 'tangent_rows', 'vertical_addition']
for name in names:
    q = 'ShielddSecurity.ConcretePointCoordinateRows01.' + name
    source += f'\nset_option pp.all true in\n#check @{q}\n#print axioms {q}\n'
dest = ROOT / 'handwritten/ConcretePointCoordinateRows01.lean'
dest.parent.mkdir(exist_ok=False)
dest.write_text(source, encoding='utf-8', newline='\n')
print(str(dest))
