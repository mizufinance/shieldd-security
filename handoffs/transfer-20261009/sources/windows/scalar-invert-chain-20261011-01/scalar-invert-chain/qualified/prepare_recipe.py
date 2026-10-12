from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-chain-20261011-04'
assert not (ROOT/'prepare.py').exists()
needle='  | .register _ => inferInstance'
replacement='  | .register index => inferInstanceAs (Decidable (index ∈ defined))'
s=(OLD/'generate_source.py').read_text();assert s.count(needle)==1
(ROOT/'generate_source.py').write_text(s.replace(needle,replacement))
subprocess.run([sys.executable,'-B',str(ROOT/'generate_source.py')],check=True)
assert (ROOT/'generated/TransferScalarInvertChain01.lean').read_text()==(OLD/'generated/TransferScalarInvertChain01.lean').read_text().replace(needle,replacement)
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-04'","POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-05'")
at=s.index("plan['artifact_policy']")
extra="""failedInvertChainFourth=DIAG/'transfer-scalar-invert-chain-20261011-04'
plan['pins'] += [pin(failedInvertChainFourth/n) for n in ['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean','runs/01-TransferScalarInvertChain01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'generator_proof_only_repair':'explicit finite Nat membership decider type','unchanged_85_source_instructions_and_contracts':True,'prior_raw_artifacts':47})
