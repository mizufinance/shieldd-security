from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-inverse-correctness-20261012-03'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarInverseCorrectness01.lean').read_text()
for term in ['zero','product']:
    old='  '+('  ' if term=='zero' else '')+'have value := congrArg (fun x : ZMod nullifierModulus => x.val) '+term
    assert source.count(old)==1
    source=source.replace(old,old+'\n'+('    ' if term=='zero' else '  ')+'dsimp only at value')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInverseCorrectness01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-inverse-correctness-shape.json').write_bytes((OLD/'context/scalar-inverse-correctness-shape.json').read_bytes())
(ROOT/'prepare_recipe_from01.py').write_bytes((OLD/'prepare_recipe_from01.py').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-03'","POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-04'")
at=s.index("plan['artifact_policy']")
extra="""failedInverse=DIAG/'transfer-scalar-inverse-correctness-20261012-03'
failedInverseNames=['prepare_recipe.py','prepare_recipe_from01.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-inverse-correctness-shape.json','handwritten/TransferScalarInverseCorrectness01.lean','project/ShielddSecurity/TransferScalarInverseCorrectness01.lean','events.jsonl','runs/01-TransferScalarInverseCorrectness01/stdout.txt']
assert (failedInverse/'runs/01-TransferScalarInverseCorrectness01/stdout.txt').exists()
plan['pins'] += [pin(failedInverse/n) for n in failedInverseNames]
if (failedInverse/'project/ShielddSecurity/TransferScalarInverseCorrectness01.olean').exists():
    plan['pins'].append(pin(failedInverse/'project/ShielddSecurity/TransferScalarInverseCorrectness01.olean'))
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'two_congrArg_beta_simplifications_added':True,'original_failed_stdout_preserved':True,'guards_statements_and_prime_reuse_unchanged':True})
