from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-01'
assert not (ROOT/'prepare.py').exists() and not (OLD/'events.jsonl').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarPowField01.lean').write_bytes((OLD/'handwritten/TransferScalarPowField01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-02'")
assert s.count('POOL.mkdir()')==1
extra="""originalInputs=inputs[:]
inputs=list({json.dumps(row,sort_keys=True,separators=(',',':')):row for row in inputs}.values())
assert {json.dumps(row,sort_keys=True,separators=(',',':')) for row in originalInputs}=={json.dumps(row,sort_keys=True,separators=(',',':')) for row in inputs}
"""
s=s.replace('POOL.mkdir()',extra+'\nPOOL.mkdir()')
at=s.index("plan['artifact_policy']")
history="""unrunPower=DIAG/'transfer-scalar-pow-field-20261012-01'
assert not (unrunPower/'events.jsonl').exists()
unrunPowerNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unrunPower/n) for n in unrunPowerNames]
"""
s=s[:at]+history+s[at:];(ROOT/'prepare.py').write_text(s)
print({'exact_duplicate_identity_records_deduplicated':True,'all_distinct_records_preserved':True,'source_proofs_and_guards_unchanged':True,'unrun_predecessor_raw_artifacts':9})
