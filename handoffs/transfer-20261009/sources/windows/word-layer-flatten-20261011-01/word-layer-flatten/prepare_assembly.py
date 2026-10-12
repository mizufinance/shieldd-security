from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-layered-object-read-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-layered-object-read-20261011-02'","CURRENT = DIAG / 'transfer-word-layer-flatten-20261011-03'"),
 ("MODULE = 'TransferWordLayeredObjectRead01'","MODULE = 'TransferWordLayerFlatten01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-layered-object-read-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-word-layer-flatten-checkpoint-20261011-03'"),
 ('assert len(fresh) == 8','assert len(fresh) == 4'),
 ("assert pool['objects'] == 123 and len(pool['inherited_public_reports']) == 1051","assert pool['objects'] == 124 and len(pool['inherited_public_reports']) == 1059"),
 ("manager_endpoint = DIAG / 'transfer-pending-saturating-capacity-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-word-layered-object-read-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-pending-saturating-capacity-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-layered-object-read-endpoint01.tar.xz'"),
 ('896bbf40b0aa01170fa13e4ffc508de0b524c1210b1e894775cb4d5006faf78a','0f12778b2350f37e70a681f75a1291ef9445d76e6aae351e6d2956a9e1eb6bc6'),
 ("tar.extractfile('reports/fresh-5-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(manager_reports) == 5','assert len(manager_reports) == 8'),
 ("'module': 'TransferPendingSaturatingCapacity01'","'module': 'TransferWordLayeredObjectRead01'"),
 ('assert len(combined_reports) == 1051','assert len(combined_reports) == 1059'),
 ('assert len(manager_selected) == 123','assert len(manager_selected) == 124'),
 ("reference = {'pending_saturating_capacity':","reference = {'word_layered_object_read':"),
 ("'imported_complete_reports': 5","'imported_complete_reports': 8"),
 ("'complete_owned_modules': 123, 'inherited_complete_reports': 1051","'complete_owned_modules': 124, 'inherited_complete_reports': 1059"),
 ("'fresh_definition_audits': 2","'fresh_definition_audits': 0"),
 ("'fresh_theorem_audits': 6","'fresh_theorem_audits': 4"),
 ("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 4"),
 ("'inherited_complete_public_audits': 1051","'inherited_complete_public_audits': 1059"),
 ("'rejected_attempts': 1","'rejected_attempts': 2"),
 ("archive = ROOT / 'portable-windows-word-layered-object-read-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-layer-flatten-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 1051","'fresh_audits': 4, 'inherited_audits': 1059",2)
s=s.replace('transfer-word-layered-object-read-endpoint-v1','transfer-word-layer-flatten-endpoint-v1').replace('one-hundred-twenty-three-module','one-hundred-twenty-four-module').replace('1051 original inherited','1059 original inherited').replace('verified 1051 inherited','verified 1059 inherited')
s=s.replace('LIVE_CHECKED_WORD_OBJECT_LAYER_STACK_SOURCE_BRANCHES_QUALIFIED','CHECKED_WORD_LOOKUP_EQUALS_FUNCTIONAL_LAYER_APPLICATION_AND_FLATTEN_QUALIFIED')
start=s.index("failed=DIAG/'transfer-word-layered-object-read-20261011-01'");end=s.index("row=mapping['saturating_capacity_source_shape']",start)
history="""for attempt in [1,2]:
    failed=DIAG/('transfer-word-layer-flatten-20261011-'+str(attempt).zfill(2))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferWordLayerFlatten01.lean','project/ShielddSecurity/TransferWordLayerFlatten01.lean']
    if attempt==1:names.append('runs/01-TransferWordLayerFlatten01/stdout.txt')
    for name in names:
        assert pin(failed/name) in plan['pins']
        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'original singleton-defeq failure01 or pre-Lean pressure02 retained; entire failed attempt zero proof/native/control credit including incomplete sorryAx output')
"""
s=s[:start]+history+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete full type/axiom reports retained, all theorems and no new definitions. Newest-first live checked lookup is exact oldest-first functional application and flatten object observation, via symbolic stack composition and local singleton-view extensional equality. No selected-value or getter-success premise; wrong type still checked panic. Failed01 singleton definitional-equality error and failed02 pre-Lean pressure retained as nineteen complete raw files, each entire failed attempt zero proof/control credit including incomplete sorryAx reports. Fresh03 same repaired source as02, unchanged limits/guards. Native liveness/locks/Clone/Any/imbl/map/ownership/time/compiler remain separate. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':1059,'owned_modules':124,'history_files':19})
