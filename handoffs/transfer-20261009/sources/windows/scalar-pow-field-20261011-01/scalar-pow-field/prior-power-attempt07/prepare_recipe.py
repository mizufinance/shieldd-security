from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-06'
assert not (ROOT/'prepare.py').exists() and not (OLD/'plan.json').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferScalarPowField01.lean').write_bytes((OLD/'handwritten/TransferScalarPowField01.lean').read_bytes())
(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-06'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-07'")
old="plan['pins'].append(mapping['scalar_inverse_correctness_source_shape'])\n"
assert s.count(old)==1;s=s.replace(old,'')
assert 'scalar_inverse_correctness_source_shape' not in s
extra="""unpreparedPowerSixth=DIAG/'transfer-scalar-pow-field-20261012-06'
assert not (unpreparedPowerSixth/'plan.json').exists() and not (unpreparedPowerSixth/'events.jsonl').exists()
unpreparedPowerSixthNames=['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unpreparedPowerSixth/n) for n in unpreparedPowerSixthNames]
plan['pins'].append(pin(DIAG/'transfer-scalar-pow-field-owned-floor-20261012-06/composition-review.json'))
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'only_stale_metadata_key_removed':True,'six_theorem_source_and_all_guards_unchanged':True,'original_setup_source_and_composition_retained':True})
