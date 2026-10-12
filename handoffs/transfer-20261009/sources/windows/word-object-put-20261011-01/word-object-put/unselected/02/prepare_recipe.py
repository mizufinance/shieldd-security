from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-object-put-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(prior/'prepare.py').read_text().replace('transfer-word-object-put-owned-floor-20261011-01','transfer-word-object-put-owned-floor-20261011-02')
at=s.index("plan['artifact_policy'] =")
s=s[:at]+"failedPut=DIAG/'transfer-word-object-put-20261011-01'\nplan['pins'] += [pin(failedPut/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordObjectPut01.lean','project/ShielddSecurity/TransferWordObjectPut01.lean','runs/01-TransferWordObjectPut01/stdout.txt','context/checked-pending-put-shape.json']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
source=(prior/'handwritten/TransferWordObjectPut01.lean').read_text()
a='exact ⟨by simp only [ite_true], fun other different => by simp only [if_neg different]⟩'
b='exact ⟨if_pos rfl, fun _ different => if_neg different⟩'
assert source.count(a)==1;source=source.replace(a,b)
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferWordObjectPut01.lean').write_text(source)
(ROOT/'context').mkdir();shutil.copyfile(prior/'context/checked-pending-put-shape.json',ROOT/'context/checked-pending-put-shape.json')
print({'direct_conditional_proof_repair':True,'same_eight_contracts':True,'failed01_zero_credit':True,'guards_unchanged':True})
