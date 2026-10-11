"""Fresh proof-only normalization of the exact spend-event cache receipt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-native-raw-pending-20261011-02'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
source=(old/'handwritten/TransferNativeRawPending01.lean').read_text()
assert source.count('  exact framed.trans staged')==1
source=source.replace('  exact framed.trans staged','  simpa only [TransferRawEffectsSource01.emitSpends_exact] using framed.trans staged')
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeRawPending01.lean').write_text(source)
s=(old/'prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-native-raw-pending-owned-floor-20261011-02'","POOL = DIAG / 'transfer-native-raw-pending-owned-floor-20261011-03'")
anchor="plan['pins'] += mapping['runtime_sources']";assert s.count(anchor)==1
extra="rejected_native_raw02=DIAG/'transfer-native-raw-pending-20261011-02'\nplan['pins'] += [pin(rejected_native_raw02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferNativeRawPending01.lean','project/ShielddSecurity/TransferNativeRawPending01.lean','runs/01-TransferNativeRawPending01/stdout.txt']]\n"
s=s.replace(anchor,extra+anchor)
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Source01 and02 strict failed, zero whole-proof credit. Source03 normalizes the original emitSpends recurrence receipt to its derived exact cache event update at the final all-return notes frame; source02 explicit sum type and exact successful-nullify receipt retained. Definitions, theorem premises/conclusions and physical/per-run guards unchanged. Both failed originals fully retained.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'failed_original_credit':0,'repair':'exact emitSpends cache normalization'})
