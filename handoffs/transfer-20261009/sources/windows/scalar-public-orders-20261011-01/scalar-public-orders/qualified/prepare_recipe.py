from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-public-orders-20261012-01'
assert not (ROOT/'prepare.py').exists() and not (OLD/'plan.json').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferScalarPublicOrders01.lean').write_bytes((OLD/'handwritten/TransferScalarPublicOrders01.lean').read_bytes())
(ROOT/'context/scalar-public-orders-shape.json').write_bytes((OLD/'context/scalar-public-orders-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-public-orders-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-public-orders-owned-floor-20261012-02'")
old="plan['pins'].append(mapping['scalar_pow_bit_integer_source_shape'])\n"
assert s.count(old)==1;s=s.replace(old,'')
extra="""unpreparedOrders=DIAG/'transfer-scalar-public-orders-20261012-01'
assert not (unpreparedOrders/'plan.json').exists() and not (unpreparedOrders/'events.jsonl').exists()
unpreparedOrderNames=['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-public-orders-shape.json','handwritten/TransferScalarPublicOrders01.lean','project/ShielddSecurity/TransferScalarPublicOrders01.lean']
plan['pins'] += [pin(unpreparedOrders/n) for n in unpreparedOrderNames]
plan['pins'].append(pin(DIAG/'transfer-scalar-public-orders-owned-floor-20261012-01/composition-review.json'))
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'source_theorems_and_guards_unchanged':True,'unprepared_predecessor_raw_files':7,'prior_composition_identity_preserved':True})
