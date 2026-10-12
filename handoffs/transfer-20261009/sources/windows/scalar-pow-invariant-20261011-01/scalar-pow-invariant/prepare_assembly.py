from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-square-product-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-square-product-20261011-02'","CURRENT = DIAG / 'transfer-scalar-pow-invariant-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-square-product-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-pow-invariant-checkpoint-20261011-01'"),
 ("MODULE = 'TransferScalarSquareProduct01'","MODULE = 'TransferScalarPowInvariant01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-square-diagonal-endpoint-20261011-04'","manager_endpoint = DIAG / 'transfer-scalar-square-product-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-square-diagonal-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-square-product-endpoint01.tar.xz'"),
 ('3eebce58e23b5202996dcc952da28cdef9fae962cc4ecaf5eb67486b1ed33f28','2ee61861b08e8142d2afc951c30b95da544f0a3dbdadbfc0051e21ef872bc62e'),
 ("'module': 'TransferScalarSquareDiagonal01'","'module': 'TransferScalarSquareProduct01'"),
 ("reference = {'scalar_square_diagonal':","reference = {'scalar_square_product':"),
 ("assert len(fresh) == 5","assert len(fresh) == 15"),
 ("assert len(manager_reports) == 4","assert len(manager_reports) == 5"),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 11 and declaration_kinds.count('theorem') == 4"),
 ("archive = ROOT / 'portable-windows-scalar-square-product-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-pow-invariant-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-15-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 154','== 155').replace('== 1217','== 1222').replace('one-hundred-fifty-four-module','one-hundred-fifty-five-module').replace('1217 original inherited complete reports','1222 original inherited complete reports').replace('verified 1217 inherited reports','verified 1222 inherited reports')
start=s.index("prior=DIAG/'transfer-scalar-square-product-20261011-01'");end=s.index("row=mapping['scalar_square_product_source_shape']",start)
s=s[:start]+"""row=mapping['scalar_pow_invariant_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-pow-invariant-shape.json','exact authenticated cached ZERO/ONE/R and reverse word/bit pow, pow_vartime and repeated-square source helper; static association only, exponent/native Choice/compiler/caller separate')
"""+s[end:]
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0").replace('transfer-scalar-square-product-endpoint-v1','transfer-scalar-pow-invariant-endpoint-v1').replace('SOURCE_OPTIMIZED_SQUARE_CARRY_AND_MONTGOMERY_CONTRACT_QUALIFIED','SOURCE_POW_LOOPS_AND_REPEATED_SQUARE_CANONICAL_INVARIANT_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Fifteen complete declarations:eleven definitions/four theorems. Exact source ZERO/ONE Montgomery key certificates; operation-derived canonical results for both modeled pow loops and repeated-square helper. Mathematical exponent and inverse semantics, native Choice/assignment and full Transfer remain open. No ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-invariant-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-square-product-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':15,'inherited_reports':1222,'owned_modules':155})
