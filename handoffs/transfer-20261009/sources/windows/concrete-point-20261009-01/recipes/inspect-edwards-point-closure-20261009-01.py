from pathlib import Path

template=Path('C:/src/shieldd-transfer-handoffs/inspect-field-concrete-closure-20261009-01.py').read_text()
template=template.replace("['ShielddSecurity.ConcreteJubjubField01']", "['Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point']")
template=template.replace('field-concrete-closure-inspection-20261009-01.json','edwards-point-closure-inspection-20261009-01.json')
exec(compile(template,__file__,'exec'))
