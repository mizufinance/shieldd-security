from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-square-diagonal-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-square-diagonal-20261011-04'","CURRENT = DIAG / 'transfer-scalar-square-product-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-square-diagonal-checkpoint-20261011-04'","CHECKPOINT = DIAG / 'transfer-scalar-square-product-checkpoint-20261011-02'"),
 ("MODULE = 'TransferScalarSquareDiagonal01'","MODULE = 'TransferScalarSquareProduct01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-square-shift-endpoint-20261011-04'","manager_endpoint = DIAG / 'transfer-scalar-square-diagonal-endpoint-20261011-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-square-shift-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-square-diagonal-endpoint01.tar.xz'"),
 ('5796296eacfe170db9b061f566f33f211f92a363a947668d49ea47c1eef73672','3eebce58e23b5202996dcc952da28cdef9fae962cc4ecaf5eb67486b1ed33f28'),
 ("'module': 'TransferScalarSquareShift01'","'module': 'TransferScalarSquareDiagonal01'"),
 ("reference = {'scalar_square_shift':","reference = {'scalar_square_diagonal':"),
 ("assert len(fresh) == 4","assert len(fresh) == 5"),
 ("assert len(manager_reports) == 7","assert len(manager_reports) == 4"),
 ("manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 2","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-scalar-square-diagonal-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-square-product-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 153','== 154').replace('== 1213','== 1217').replace('one-hundred-fifty-three-module','one-hundred-fifty-four-module').replace('1213 original inherited complete reports','1217 original inherited complete reports').replace('verified 1213 inherited reports','verified 1217 inherited reports')
start=s.index('for attempt in [1,2,3]:');end=s.index("row=mapping['scalar_square_diagonal_source_shape']",start)
s=s[:start]+"""prior=DIAG/'transfer-scalar-square-product-20261011-01'
names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-product-shape.json','handwritten/TransferScalarSquareProduct01.lean','project/ShielddSecurity/TransferScalarSquareProduct01.lean']
assert not (prior/'runs/01-TransferScalarSquareProduct01/stdout.txt').exists()
for name in names:
    row=pin(prior/name)
    assert row in plan['pins']
    add(prior/name,'prior-square-product-attempt01/'+name,'original physical memory pressure attempt;10 original raw artifacts, no Lean stdout or module result, not a successful control')
row=mapping['scalar_square_product_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-product-shape.json','exact authenticated cached optimized square MAC/shift/ADC/final reduction body; static association only')
"""+s[end:]
s=s.replace("'rejected_attempts': 2, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 1","'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0").replace('transfer-scalar-square-diagonal-endpoint-v1','transfer-scalar-square-product-endpoint-v1').replace('SOURCE_DIAGONAL_MAC_ADC_RECURRENCE_AND_ALGEBRAIC_SQUARE_QUALIFIED','SOURCE_OPTIMIZED_SQUARE_CARRY_AND_MONTGOMERY_CONTRACT_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete declarations:two definitions/three theorems. Original10 raw pressure-attempt artifacts retained. Same source definitions/proofs/contracts and finite guards; no ancestors replayed. This establishes the optimized arithmetic square contract, while full native and Transfer completion remain separate.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-square-product-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-square-diagonal-checkpoint-20261011-04/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1217,'owned_modules':154})
