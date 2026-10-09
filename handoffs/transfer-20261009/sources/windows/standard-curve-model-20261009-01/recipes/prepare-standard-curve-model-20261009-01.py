from pathlib import Path
local=Path('C:/src/shieldd-transfer-handoffs')
diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
prior=diag/'windows-tangent-point-transport-20261009-01-kernel'
assert (prior/'complete.txt').exists() and (prior/'exit.txt').read_text().strip()=='0'
body=(local/'prepare-tangent-point-transport-generated-20261009-01.py').read_text()
for old,new in [
 ('tangent-point-transport-20261009-01','standard-curve-model-20261009-01'),
 ('tangent-point-transport-closure-20261009-01','standard-curve-model-closure-20261009-01'),
 ('tangent-point-transport-closure-inspection-20261009-01','standard-curve-model-closure-inspection-20261009-01'),
 ('tangent-point-transport-cache-20261009-01','standard-curve-model-cache-20261009-01'),
 ('tangent-point-transport-boundary-2026100901','standard-curve-model-boundary-2026100901'),
 ('TransferOwnedTangentPointTransportBoundary2026100901','TransferOwnedStandardCurveModelBoundary2026100901'),
 ('ConcreteTangentAddition01','ConcreteStandardCurveModel01'),
]:body=body.replace(old,new)
old="for namespace in ['windows-tangent-rational-20261009-01'"
assert body.count(old)==1
body=body.replace(old,"for namespace in ['windows-tangent-point-transport-20261009-01','windows-tangent-rational-20261009-01'",1)
start=body.index("scope='");end=body.index('\nbody=re.sub',start)
body=body[:start]+"scope='All-pairs Edwards addition compatibility and concrete StandardCurveModel over the actual Mathlib elliptic Point group, with all affine Edwards solutions covered. No assumed morphism, order, cardinality, or native representation premise. Scalar trace, point order, cardinality, native codec and other full Transfer G2-G5/G7 obligations OPEN.'"+body[end:]
target=local/'prepare-standard-curve-model-generated-20261009-01.py'
assert not target.exists();target.write_text(body)
exec(compile(body,str(target),'exec'),{'__file__':str(target),'__name__':'__main__'})
