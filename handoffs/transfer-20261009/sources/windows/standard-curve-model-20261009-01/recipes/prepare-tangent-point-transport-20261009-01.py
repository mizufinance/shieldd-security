from pathlib import Path
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
for stem in ['windows-secant-point-transport-20261009-01','windows-tangent-rational-20261009-01']:
    prior=diag/(stem+'-kernel')
    assert (prior/'complete.txt').exists() and (prior/'exit.txt').read_text().strip()=='0'
body=(local/'prepare-secant-point-transport-generated-20261009-01.py').read_text()
for old,new in [
 ('secant-point-transport-20261009-01','tangent-point-transport-20261009-01'),
 ('secant-point-transport-closure-20261009-01','tangent-point-transport-closure-20261009-01'),
 ('secant-point-transport-closure-inspection-20261009-01','tangent-point-transport-closure-inspection-20261009-01'),
 ('secant-point-transport-cache-20261009-01','tangent-point-transport-cache-20261009-01'),
 ('secant-point-transport-boundary-2026100901','tangent-point-transport-boundary-2026100901'),
 ('TransferOwnedSecantPointTransportBoundary2026100901','TransferOwnedTangentPointTransportBoundary2026100901'),
 ('ConcreteSecantAddition01','ConcreteTangentAddition01'),
]:body=body.replace(old,new)
old="for namespace in ['windows-secant-rational-20261009-02'"
assert body.count(old)==1
body=body.replace(old,"for namespace in ['windows-tangent-rational-20261009-01','windows-secant-point-transport-20261009-01','windows-secant-rational-20261009-02'",1)
start=body.index("scope='");end=body.index('\nbody=re.sub',start)
body=body[:start]+"scope='Concrete Edwards doubling transport to actual Mathlib Point for nonzero input x and nonzero doubling cross numerator. Input and output membership, nonzero denominators, tangent slope and output rows are derived. All-pairs case assembly, StandardCurveModel, order, cardinality, native codec, and full Transfer OPEN.'"+body[end:]
target=local/'prepare-tangent-point-transport-generated-20261009-01.py'
assert not target.exists();target.write_text(body)
exec(compile(body,str(target),'exec'),{'__file__':str(target),'__name__':'__main__'})
