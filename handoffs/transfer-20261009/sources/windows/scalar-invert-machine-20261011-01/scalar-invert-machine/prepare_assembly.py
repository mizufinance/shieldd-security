from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-pow-invariant-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-pow-invariant-20261011-01'","CURRENT = DIAG / 'transfer-scalar-invert-machine-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-pow-invariant-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-scalar-invert-machine-checkpoint-20261011-01'"),
 ("MODULE = 'TransferScalarPowInvariant01'","MODULE = 'TransferScalarInvertMachine01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-square-product-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-pow-invariant-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-square-product-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-pow-invariant-endpoint01.tar.xz'"),
 ('2ee61861b08e8142d2afc951c30b95da544f0a3dbdadbfc0051e21ef872bc62e','a931f28536968c8fcaa746a26d696216e663432e303178439f92dddd22b83687'),
 ("'module': 'TransferScalarSquareProduct01'","'module': 'TransferScalarPowInvariant01'"),
 ("reference = {'scalar_square_product':","reference = {'scalar_pow_invariant':"),
 ("assert len(fresh) == 15","assert len(fresh) == 20"),
 ("assert len(manager_reports) == 5","assert len(manager_reports) == 15"),
 ("manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-15-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 11 and declaration_kinds.count('theorem') == 4","assert declaration_kinds.count('def') == 14 and declaration_kinds.count('inductive') == 2 and declaration_kinds.count('theorem') == 4"),
 ("archive = ROOT / 'portable-windows-scalar-pow-invariant-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-invert-machine-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-15-complete-declarations.txt'","add(stdout, 'reports/fresh-20-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 155','== 156').replace('== 1222','== 1237').replace('one-hundred-fifty-five-module','one-hundred-fifty-six-module').replace('1222 original inherited complete reports','1237 original inherited complete reports').replace('verified 1222 inherited reports','verified 1237 inherited reports')
replace("row=mapping['scalar_pow_invariant_source_shape']","row=mapping['scalar_invert_machine_source_shape']\nassert pin(row['path'])==row and row in plan['pins']\nadd(row['path'],'context/scalar-invert-machine-shape.json','exact authenticated cached source inversion addition chain and repeated-square helper; generic symbolic machine only, exact source instance/inverse/native binding separate')\nrow=mapping['scalar_pow_invariant_source_shape']")
s=s.replace('transfer-scalar-pow-invariant-endpoint-v1','transfer-scalar-invert-machine-endpoint-v1').replace('SOURCE_POW_LOOPS_AND_REPEATED_SQUARE_CANONICAL_INVARIANT_QUALIFIED','SYMBOLIC_INVERSION_REGISTER_MACHINE_INITIALIZED_READS_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Twenty complete declarations:two inductives/fourteen definitions/four theorems. Canonical word/exponent register machines share source instruction forms; well-formed symbolic source reads derive successful canonical output state without uninitialized reads. Natural-exponent machine alone is not field exponent proof; actual fixed instance and native/inverse/full Transfer remain open. No ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-invert-machine-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-pow-invariant-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':20,'inherited_reports':1237,'owned_modules':156})
