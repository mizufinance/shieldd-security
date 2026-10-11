from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
prior=DIAG/'transfer-word-object-read-20261011-01'
assert not (prior/'events.jsonl').exists() and not (ROOT/'prepare_recipe.py').exists()
s=(prior/'prepare_recipe.py').read_text().replace('transfer-word-object-read-owned-floor-20261011-01','transfer-word-object-read-owned-floor-20261011-02')
s=s.replace("(ROOT/'handwritten').mkdir()","(ROOT/'handwritten').mkdir(exist_ok=True)")
s=s.replace("(ROOT/'prepare.py').write_text(s)","at=s.index(\"plan['artifact_policy'] =\")\ns=s[:at]+\"unrunRead=DIAG/'transfer-word-object-read-20261011-01'\\nassert not (unrunRead/'events.jsonl').exists()\\nplan['pins'] += [pin(unrunRead/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferWordObjectRead01.lean','project/ShielddSecurity/TransferWordObjectRead01.lean','context/checked-pending-read-shape.json']]\\n\"+s[at:]\n(ROOT/'prepare.py').write_text(s)")
(ROOT/'prepare_recipe.py').write_text(s)
(ROOT/'handwritten').mkdir()
source=(prior/'handwritten/TransferWordObjectRead01.lean').read_text()
source=source.replace('cases selected : writes key <;> rfl','cases selected : writes key <;> simp only [overlay, selected]')
(ROOT/'handwritten/TransferWordObjectRead01.lean').write_text(source)
print({'setup_mkdir_repaired':True,'setup01_unrun':True,'overlay_proof_uses_exact_selected_entry':True})
