from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-checked-word-block-driver-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-checked-word-block-driver-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-block-driver-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"failedCheckedBlock=DIAG/'transfer-checked-word-block-driver-20261011-01'\nplan['pins'] += [pin(failedCheckedBlock/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordBlockDriver01.lean','project/ShielddSecurity/TransferCheckedWordBlockDriver01.lean','runs/01-TransferCheckedWordBlockDriver01/stdout.txt']]\n"+s[at:]
source=(OLD/'handwritten/TransferCheckedWordBlockDriver01.lean').read_text()
prefix='    | ok staged =>\n'
assert source.count(prefix)==1
source=source.replace(prefix,prefix+'      change (sealAtKey parent staged key).map (fun result => result.mapError (fun _ => BatchError.sealed)) = .ok (.ok final) at returned\n')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferCheckedWordBlockDriver01.lean').write_text(source)
(ROOT/'prepare.py').write_text(s)
print({'bound_result_match_normalization_only':True,'failed_raw_files':10,'same_definitions_contracts_guards':True})
