from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-pending-saturating-capacity-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-pending-saturating-capacity-20261011-01'","CURRENT = DIAG / 'transfer-word-layered-object-read-20261011-02'"),
 ("MODULE = 'TransferPendingSaturatingCapacity01'","MODULE = 'TransferWordLayeredObjectRead01'"),
 ("CHECKPOINT = DIAG / 'transfer-pending-saturating-capacity-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-word-layered-object-read-checkpoint-20261011-02'"),
 ('assert len(fresh) == 5','assert len(fresh) == 8'),
 ("assert pool['objects'] == 122 and len(pool['inherited_public_reports']) == 1046","assert pool['objects'] == 123 and len(pool['inherited_public_reports']) == 1051"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-publication-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-pending-saturating-capacity-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-publication-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-pending-saturating-capacity-endpoint01.tar.xz'"),
 ('cb74f5998c1bcb16a2c6f9ad6d9525a62dd46ee124b813ee7634c432f041be7a','896bbf40b0aa01170fa13e4ffc508de0b524c1210b1e894775cb4d5006faf78a'),
 ("tar.extractfile('reports/fresh-2-complete-declarations.txt')","tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ('assert len(manager_reports) == 2','assert len(manager_reports) == 5'),
 ("'module': 'TransferCheckedWordPublication01'","'module': 'TransferPendingSaturatingCapacity01'"),
 ('assert len(combined_reports) == 1046','assert len(combined_reports) == 1051'),
 ('assert len(manager_selected) == 122','assert len(manager_selected) == 123'),
 ("reference = {'checked_word_publication':","reference = {'pending_saturating_capacity':"),
 ("'imported_complete_reports': 2","'imported_complete_reports': 5"),
 ("'complete_owned_modules': 122, 'inherited_complete_reports': 1046","'complete_owned_modules': 123, 'inherited_complete_reports': 1051"),
 ("'fresh_definition_audits': 1","'fresh_definition_audits': 2"),
 ("'fresh_theorem_audits': 4","'fresh_theorem_audits': 6"),
 ("'fresh_complete_public_audits': 5","'fresh_complete_public_audits': 8"),
 ("'inherited_complete_public_audits': 1046","'inherited_complete_public_audits': 1051"),
 ("'rejected_attempts': 0","'rejected_attempts': 1"),
 ("archive = ROOT / 'portable-windows-pending-saturating-capacity-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-layered-object-read-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 5, 'inherited_audits': 1046","'fresh_audits': 8, 'inherited_audits': 1051",2)
s=s.replace('transfer-pending-saturating-capacity-endpoint-v1','transfer-word-layered-object-read-endpoint-v1').replace('one-hundred-twenty-two-module','one-hundred-twenty-three-module').replace('1046 original inherited','1051 original inherited').replace('verified 1046 inherited','verified 1051 inherited')
s=s.replace('FINITE_WIDTH_PENDING_SATURATING_CAPACITY_GATE_EXACT_SUM_BOUND_QUALIFIED','LIVE_CHECKED_WORD_OBJECT_LAYER_STACK_SOURCE_BRANCHES_QUALIFIED')
at=s.index("row=mapping['saturating_capacity_source_shape']")
s=s[:at]+"failed=DIAG/'transfer-word-layered-object-read-20261011-01'\nfor name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayeredObjectRead01.lean','project/ShielddSecurity/TransferWordLayeredObjectRead01.lean']:\n    assert pin(failed/name) in plan['pins']\n    add(failed/name,'unselected/01/'+name,'original pre-Lean physical pressure stop retained; zero proof/native/control credit')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained, two definitions/six theorems. Source-shaped checked leaf/newest-layer/parent recurrence preserves latest map-hit precedence, tombstone absence and wrong-type/applied-layer panic distinctions. Symbolic live stack derives selected-value result without caller selected object/getter success. Original pressure01 before Lean preserved as nine complete raw files with zero credit; fresh02 exact same source and guards. Native layer liveness/locks/Any/downcast/Clone/aliasing/time/compiler and functional StateDelta equivalence remain separate. Panic sentinel is non-returning native branch, never Rust Result or executed control. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1051,'owned_modules':123,'pressure_history_files':9})
