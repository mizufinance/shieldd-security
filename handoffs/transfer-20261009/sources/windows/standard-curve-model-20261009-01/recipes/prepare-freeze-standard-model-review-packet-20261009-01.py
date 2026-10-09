from pathlib import Path
local=Path('C:/src/shieldd-transfer-handoffs')
body=(local/'freeze-addition-next-review-packet-20261009-01.py').read_text()
body=body.replace("dest = local / ('addition-next-review-packet-20261009-' + args.pole_run)","dest = local / 'standard-model-review-packet-20261009-01'")
old="    ('pole-point-transport', args.pole_run, 'pole-point-transport', ['ConcretePoleAddition01']),\n]"
new="""    ('pole-point-transport', args.pole_run, 'pole-point-transport', ['ConcretePoleAddition01']),
    ('secant-polynomials', '01', 'secant-polynomials', ['EdwardsSecantPolynomials01']),
    ('secant-rational', '02', 'secant-rational', ['EdwardsSecantRational01']),
    ('secant-point-transport', '01', 'secant-point-transport', ['ConcreteSecantAddition01']),
    ('tangent-rational', '01', 'tangent-rational', ['EdwardsTangentPolynomials01','EdwardsTangentRational01']),
    ('tangent-point-transport', '01', 'tangent-point-transport', ['ConcreteTangentAddition01']),
    ('standard-curve-model', '01', 'standard-curve-model', ['ConcreteStandardCurveModel01']),
]"""
assert old in body;body=body.replace(old,new)
body=body.replace("assert len(modules) == 7 and sum(v['audit']['audits'] for v in modules.values()) == 36", "assert len(modules) == 14 and sum(v['audit']['audits'] for v in modules.values()) == 54")
body=body.replace("'fresh_modules': 7", "'fresh_modules': 14").replace("'declaration_audits': 36", "'declaration_audits': 54")
body=body.replace("'Edwards addition transport for every vanishing cross numerator'", "'Edwards addition transport for every vanishing cross numerator', 'regular secant and tangent polynomial and rational rows', 'regular secant and tangent transport to actual Mathlib Point', 'all-pairs addition compatibility', 'actual Mathlib Point StandardCurveModel with coverage of all Edwards curve solutions'")
body=body.replace("'general regular secant/tangent addition homomorphism', 'StandardCurveModel', 'scalar trace'", "'scalar trace'")
body=body.replace("'marker': 'TRANSFER_ADDITION_NEXT_REVIEW_PACKET_V1'", "'marker': 'TRANSFER_STANDARD_MODEL_REVIEW_PACKET_V1'")
old="write('dependency-resolution.json', list(dependencies.values()))"
extra="""for filename in [
    'prepare-secant-polynomials-20261009-01.py','prepare-secant-polynomials-generated-20261009-01.py',
    'prepare-secant-rational-20261009-01.py','prepare-secant-rational-generated-20261009-01.py',
    'prepare-secant-rational-successor-20261009-02.py','prepare-secant-rational-generated-20261009-02.py',
    'prepare-secant-point-transport-20261009-01.py','prepare-secant-point-transport-generated-20261009-01.py',
    'prepare-tangent-rational-20261009-01.py','prepare-tangent-rational-generated-20261009-01.py',
    'prepare-tangent-point-transport-20261009-01.py','prepare-tangent-point-transport-generated-20261009-01.py',
    'prepare-standard-curve-model-20261009-01.py','prepare-standard-curve-model-generated-20261009-01.py',
    'generate-edwards-secant-polynomials-20261009-01.py','generate-edwards-tangent-polynomials-20261009-01.py',
    'prepare-freeze-standard-model-review-packet-20261009-01.py',
]:
    copy(local/filename,'recipes/'+filename)
for filename in ['edwards-secant-polynomial-generation-20261009-01.json','edwards-tangent-polynomial-generation-20261009-01.json']:
    record=load(local/filename)
    module='EdwardsSecantPolynomials01' if 'secant' in filename else 'EdwardsTangentPolynomials01'
    assert record['source_sha256']==modules[module]['audit']['original_source_sha256']
    copy(local/filename,'generation-inputs/'+filename)
"""
body=body.replace(old,extra+old)
body=body.replace("'pole-point-transport01': 'missing denominator unfolding in polynomial proof; batch zero credit'", "'pole-point-transport01': 'missing denominator unfolding in polynomial proof; batch zero credit', 'secant-rational01': 'No goals to be solved compiler failures in four helper steps; batch zero credit; accidental polynomial replay does not count as new credit'")
target=local/'freeze-standard-model-review-packet-20261009-01.py'
assert not target.exists();target.write_text(body)
exec(compile(body,str(target),'exec'),{'__file__':str(target),'__name__':'__main__'})
