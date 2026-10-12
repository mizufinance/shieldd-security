from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-square-cross-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-square-cross-20261011-02'","CURRENT = DIAG / 'transfer-scalar-square-shift-20261011-04'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-square-cross-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-square-shift-checkpoint-20261011-04'"),
 ("MODULE = 'TransferScalarSquareCross01'","MODULE = 'TransferScalarSquareShift01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-input-family-endpoint-20261011-04'","manager_endpoint = DIAG / 'transfer-scalar-square-cross-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-input-family-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-square-cross-endpoint01.tar.xz'"),
 ('1fd09e6666ffe57133f74f181777e702e48d92f0a5ecf529b6535c93bcb2a6a5','1e59553533150fea47a2af10e7f75454138f0a9f84795420938dba1611390d34'),
 ("'module': 'TransferScalarInputFamily01'","'module': 'TransferScalarSquareCross01'"),
 ("reference = {'scalar_input_family':","reference = {'scalar_square_cross':"),
 ("assert len(fresh) == 6","assert len(fresh) == 7"),
 ("assert len(manager_reports) == 5","assert len(manager_reports) == 6"),
 ("manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 5"),
 ("archive = ROOT / 'portable-windows-scalar-square-cross-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-square-shift-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-7-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 151','== 152').replace('== 1200','== 1206').replace('one-hundred-fifty-one-module','one-hundred-fifty-two-module').replace('1200 original inherited complete reports','1206 original inherited complete reports').replace('verified 1200 inherited reports','verified 1206 inherited reports')
start=s.index("failed=DIAG/'transfer-scalar-square-cross-20261011-01'");end=s.index("row=mapping['scalar_square_cross_source_shape']",start)
s=s[:start]+"""for attempt in [1,2,3]:
    prior=DIAG/('transfer-scalar-square-shift-20261011-0'+str(attempt))
    names=['prepare_recipe.py']
    if attempt==1: names.append('handwritten/TransferScalarSquareShift01.lean')
    if attempt==2:
        names+=['prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-shift-shape.json','handwritten/TransferScalarSquareShift01.lean','project/ShielddSecurity/TransferScalarSquareShift01.lean','runs/01-TransferScalarSquareShift01/stdout.txt']
    else: assert not (prior/'plan.json').exists()
    for name in names:
        row=pin(prior/name)
        assert row in plan['pins']
        add(prior/name,'prior-square-shift-attempt0'+str(attempt)+'/'+name,'original source capture delimiter setup failure, reserved local token Lean failure or failed rename recipe precondition;14 original raw artifacts total, zero credit, not negative controls')
row=mapping['scalar_square_shift_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-shift-shape.json','exact authenticated cached seven adjacent source shift assignments and remaining square body; static association only')
"""+s[end:]
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0","'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 2").replace('transfer-scalar-square-cross-endpoint-v1','transfer-scalar-square-shift-endpoint-v1').replace('SOURCE_SIX_MAC_SQUARE_CROSS_PREFIX_EXACT_INTEGER_QUALIFIED','SOURCE_ADJACENT_SHIFTS_DERIVE_EXACT_DOUBLED_CROSS_INTEGER_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete declarations:two definitions/five theorems. Original14 raw setup/proof failure artifacts retained zero credit; capture delimiter and exact local reserved identifier repairs. Source definitions/contracts/finite guards unchanged; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-square-shift-checkpoint-20261011-04';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-square-cross-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':7,'inherited_reports':1206,'owned_modules':152})
