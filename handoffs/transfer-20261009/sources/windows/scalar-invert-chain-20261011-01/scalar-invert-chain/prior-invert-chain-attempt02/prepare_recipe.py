from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-invert-chain-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'generate_source.py').write_bytes((OLD/'generate_source.py').read_bytes())
subprocess.run([sys.executable,'-B',str(ROOT/'generate_source.py')],check=True)
assert (ROOT/'generated/TransferScalarInvertChain01.lean').read_bytes()==(OLD/'generated/TransferScalarInvertChain01.lean').read_bytes()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-invert-chain-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""pressureInvertChain=DIAG/'transfer-scalar-invert-chain-20261011-01'
priorChainNames=['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean']
if (pressureInvertChain/'runs/01-TransferScalarInvertChain01/stdout.txt').exists():
    priorChainNames.append('runs/01-TransferScalarInvertChain01/stdout.txt')
plan['pins'] += [pin(pressureInvertChain/n) for n in priorChainNames]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'source_regenerated_through_identical_generator':True,'identical_generated_Lean':True,'same_finite_guards':True,'original_pressure_history_retained':True})
