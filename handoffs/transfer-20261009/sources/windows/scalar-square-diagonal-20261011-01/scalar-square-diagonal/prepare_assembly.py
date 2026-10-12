from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-square-shift-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-square-shift-20261011-04'","CURRENT = DIAG / 'transfer-scalar-square-diagonal-20261011-04'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-square-shift-checkpoint-20261011-04'","CHECKPOINT = DIAG / 'transfer-scalar-square-diagonal-checkpoint-20261011-04'"),
 ("MODULE = 'TransferScalarSquareShift01'","MODULE = 'TransferScalarSquareDiagonal01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-square-cross-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-square-shift-endpoint-20261011-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-square-cross-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-square-shift-endpoint01.tar.xz'"),
 ('1e59553533150fea47a2af10e7f75454138f0a9f84795420938dba1611390d34','5796296eacfe170db9b061f566f33f211f92a363a947668d49ea47c1eef73672'),
 ("'module': 'TransferScalarSquareCross01'","'module': 'TransferScalarSquareShift01'"),
 ("reference = {'scalar_square_cross':","reference = {'scalar_square_shift':"),
 ("assert len(fresh) == 7","assert len(fresh) == 4"),
 ("assert len(manager_reports) == 6","assert len(manager_reports) == 7"),
 ("manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 5","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 2"),
 ("archive = ROOT / 'portable-windows-scalar-square-shift-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-square-diagonal-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-7-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 152','== 153').replace('== 1206','== 1213').replace('one-hundred-fifty-two-module','one-hundred-fifty-three-module').replace('1206 original inherited complete reports','1213 original inherited complete reports').replace('verified 1206 inherited reports','verified 1213 inherited reports')
start=s.index('for attempt in [1,2,3]:');end=s.index("row=mapping['scalar_square_shift_source_shape']",start)
s=s[:start]+"""for attempt in [1,2,3]:
    prior=DIAG/('transfer-scalar-square-diagonal-20261011-0'+str(attempt))
    names=['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-square-diagonal-shape.json','handwritten/TransferScalarSquareDiagonal01.lean','project/ShielddSecurity/TransferScalarSquareDiagonal01.lean']
    if attempt!=2:
        names+=['plan.json','review.json','events.jsonl','runs/01-TransferScalarSquareDiagonal01/stdout.txt']
    else: assert not (prior/'plan.json').exists()
    for name in names:
        row=pin(prior/name)
        assert row in plan['pins']
        add(prior/name,'prior-square-diagonal-attempt0'+str(attempt)+'/'+name,'original physical pressure attempt including empty stdout, unprepared successor with incorrect missing-stdout precondition, or Lean distribution/ADC-zero rewrite failure;29 original raw artifacts total, retained without treating failures as successful controls')
row=mapping['scalar_square_diagonal_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-diagonal-shape.json','exact authenticated cached four diagonal MAC/ADC pairs and remaining square body; static association only')
"""+s[end:]
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 2","'rejected_attempts': 2, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 1").replace('transfer-scalar-square-shift-endpoint-v1','transfer-scalar-square-diagonal-endpoint-v1').replace('SOURCE_ADJACENT_SHIFTS_DERIVE_EXACT_DOUBLED_CROSS_INTEGER_QUALIFIED','SOURCE_DIAGONAL_MAC_ADC_RECURRENCE_AND_ALGEBRAIC_SQUARE_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete declarations:two definitions/two theorems. Original29 raw pressure/setup/proof history artifacts retained; explicit term distribution and ADC zero input simplification proof-only repairs. Source definitions/contracts/finite guards unchanged; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-square-diagonal-checkpoint-20261011-04';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-square-shift-checkpoint-20261011-04/preservation_check.py').read_bytes())
print({'fresh_reports':4,'inherited_reports':1213,'owned_modules':153})
