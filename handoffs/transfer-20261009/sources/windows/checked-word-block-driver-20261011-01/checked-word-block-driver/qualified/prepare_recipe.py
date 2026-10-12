from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-checked-word-block-driver-20261011-02'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-checked-word-block-driver-owned-floor-20261011-02'","POOL = DIAG / 'transfer-checked-word-block-driver-owned-floor-20261011-03'")
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"failedCheckedBlockSecond=DIAG/'transfer-checked-word-block-driver-20261011-02'\nplan['pins'] += [pin(failedCheckedBlockSecond/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordBlockDriver01.lean','project/ShielddSecurity/TransferCheckedWordBlockDriver01.lean','runs/01-TransferCheckedWordBlockDriver01/stdout.txt']]\n"+s[at:]
source=(OLD/'handwritten/TransferCheckedWordBlockDriver01.lean').read_text()
assert source.count('exact ⟨staged, rfl, rfl⟩')==1
source=source.replace('exact ⟨staged, rfl, rfl⟩','exact ⟨staged, rfl, sealing⟩')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferCheckedWordBlockDriver01.lean').write_text(source)
(ROOT/'prepare.py').write_text(s)
print({'actual_seal_witness_equation_only':True,'failed_raw_files':20,'same_definitions_contracts_guards':True})
