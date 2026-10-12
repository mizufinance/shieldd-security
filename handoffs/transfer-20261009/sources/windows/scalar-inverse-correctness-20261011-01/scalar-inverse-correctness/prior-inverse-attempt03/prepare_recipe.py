from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-inverse-correctness-20261012-02'
assert not (ROOT/'prepare.py').exists() and not (OLD/'events.jsonl').exists()
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInverseCorrectness01.lean').write_bytes((OLD/'handwritten/TransferScalarInverseCorrectness01.lean').read_bytes())
(ROOT/'context').mkdir();(ROOT/'context/scalar-inverse-correctness-shape.json').write_bytes((OLD/'context/scalar-inverse-correctness-shape.json').read_bytes())
(ROOT/'prepare_recipe_from01.py').write_bytes((OLD/'prepare_recipe_from01.py').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-02'","POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-03'")
old='One source and bounded reports/object; complete one-hundred-sixty-one-module owned root and reachable core floor.'
new='One source and bounded reports/object; complete202-module owned root: original162-module word closure plus qualified40-module prime-tree branch, with the unchanged original qualified Mathlib/core floor.'
assert s.count(old)==1;s=s.replace(old,new)
at=s.index("plan['artifact_policy']")
extra="""unrunInverse=DIAG/'transfer-scalar-inverse-correctness-20261012-02'
assert not (unrunInverse/'events.jsonl').exists()
unrunInverseNames=['prepare_recipe.py','prepare_recipe_from01.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-inverse-correctness-shape.json','handwritten/TransferScalarInverseCorrectness01.lean','project/ShielddSecurity/TransferScalarInverseCorrectness01.lean']
plan['pins'] += [pin(unrunInverse/n) for n in unrunInverseNames]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'artifact_metadata_count_corrected_to':202,'source_proof_and_guards_unchanged':True,'unrun_predecessor_raw_artifacts':10})
