from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-publication-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-publication-20261011-01'","CURRENT = DIAG / 'transfer-pending-saturating-capacity-20261011-01'"),
 ("MODULE = 'TransferCheckedWordPublication01'","MODULE = 'TransferPendingSaturatingCapacity01'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-publication-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-pending-saturating-capacity-checkpoint-20261011-01'"),
 ('assert len(fresh) == 2','assert len(fresh) == 5'),
 ("assert pool['objects'] == 121 and len(pool['inherited_public_reports']) == 1044","assert pool['objects'] == 122 and len(pool['inherited_public_reports']) == 1046"),
 ("manager_endpoint = DIAG / 'transfer-word-object-read-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-checked-word-publication-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-object-read-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-publication-endpoint01.tar.xz'"),
 ('c3974f41d5c2f922066f6119017936606042633c1a0b97f5ed41792c219082e9','cb74f5998c1bcb16a2c6f9ad6d9525a62dd46ee124b813ee7634c432f041be7a'),
 ("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-2-complete-declarations.txt')"),
 ('assert len(manager_reports) == 8','assert len(manager_reports) == 2'),
 ("'module': 'TransferWordObjectRead01'","'module': 'TransferCheckedWordPublication01'"),
 ('assert len(combined_reports) == 1044','assert len(combined_reports) == 1046'),
 ('assert len(manager_selected) == 121','assert len(manager_selected) == 122'),
 ("reference = {'word_object_read':","reference = {'checked_word_publication':"),
 ("'imported_complete_reports': 8","'imported_complete_reports': 2"),
 ("'complete_owned_modules': 121, 'inherited_complete_reports': 1044","'complete_owned_modules': 122, 'inherited_complete_reports': 1046"),
 ("'fresh_theorem_audits': 1","'fresh_theorem_audits': 4"),
 ("'fresh_complete_public_audits': 2","'fresh_complete_public_audits': 5"),
 ("'inherited_complete_public_audits': 1044","'inherited_complete_public_audits': 1046"),
 ("archive = ROOT / 'portable-windows-checked-word-publication-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-pending-saturating-capacity-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-2-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 2, 'inherited_audits': 1044","'fresh_audits': 5, 'inherited_audits': 1046",2)
s=s.replace('transfer-checked-word-publication-endpoint-v1','transfer-pending-saturating-capacity-endpoint-v1').replace('one-hundred-twenty-one-module','one-hundred-twenty-two-module').replace('1044 original inherited','1046 original inherited').replace('verified 1044 inherited','verified 1046 inherited')
s=s.replace('RETURNED_WHOLE_WORD_DRIVER_DERIVES_CHECKED_PENDING_GETTER_AND_BOUNDARY_QUALIFIED','FINITE_WIDTH_PENDING_SATURATING_CAPACITY_GATE_EXACT_SUM_BOUND_QUALIFIED')
at=s.index("row=mapping['checked_pending_read_source_shape']")
s=s[:at]+"row=mapping['saturating_capacity_source_shape']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'],'context/saturating-capacity-shape.json','exact source pending length saturating_add comparison and consensus32768 literal; static association only')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five first-pass complete full type/axiom reports retained, one definition/four theorems. Finite-width modeled saturating addition cannot admit count above consensus limit; both 32 and 64-bit ceiling headroom certified. Generic accepted bound implies exact natural sum and each individual length bound. No actual usize ABI/operator/vector length/compiler semantics inferred from pinned comparison. Previous histories remain original ancestors; no replay/native/control/certification credit. Full Transfer OPEN.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':5,'inherited_reports':1046,'owned_modules':122,'first_pass':True})
