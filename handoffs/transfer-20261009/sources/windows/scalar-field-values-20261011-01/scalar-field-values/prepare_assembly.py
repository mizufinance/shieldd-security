from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-extended-family-endpoint-20261012-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-extended-family-20261012-01'","CURRENT = DIAG / 'transfer-scalar-field-values-20261012-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-extended-family-checkpoint-20261012-01'","CHECKPOINT = DIAG / 'transfer-scalar-field-values-checkpoint-20261012-01'"),
 ("MODULE = 'TransferScalarExtendedFamily01'","MODULE = 'TransferScalarFieldValues01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-public-constants-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-extended-family-endpoint-20261012-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-public-constants-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-extended-family-endpoint01.tar.xz'"),
 ('86fe9931d47919832ca078095ff47f6bae52162b279b66dfaab6d6a7c3d04989','68d7ab736e5e02c82a8e2bacb2a092edbfa2f3888e465434b1002d10d7b77448'),
 ("'module': 'TransferScalarPublicConstants01'","'module': 'TransferScalarExtendedFamily01'"),
 ("reference = {'scalar_public_constants':","reference = {'scalar_extended_family':"),
 ('assert len(manager_reports) == 6','assert len(manager_reports) == 4'),
 ("manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ("assert declaration_kinds.count('inductive') == 1 and declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 2","assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 4"),
 ("archive = ROOT / 'portable-windows-scalar-extended-family-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-field-values-endpoint01.tar.xz'")]:replace(a,b)
s=s.replace('== 159','== 160').replace('== 1275','== 1279').replace('one-hundred-fifty-nine-module','one-hundred-sixty-module').replace('1275 original inherited complete reports','1279 original inherited complete reports').replace('verified 1275 inherited reports','verified 1279 inherited reports')
marker="row=mapping['scalar_extended_family_source_shape']"
replace(marker,"row=mapping['scalar_field_values_source_shape']\nassert pin(row['path'])==row and row in plan['pins']\nadd(row['path'],'context/scalar-field-values-shape.json','exact qualified word operation source contracts and mathematical scope; modular proof derives field values, native compiler/caller binding separate')\n"+marker)
old=' Four complete declarations:one inductive/one definition/two theorems. Every successfully constructed represented program derives canonical raw fields and exact32-byte key; inversion refusal derives earlier construction failure or exact source zero payload. Explicit source API constructor inventory and exclusions retained. Native Choice/RNG/ct_eq/compiler/caller/helper trace, field exponent/inverse and full Transfer remain open. No ancestors replayed.'
new=' Four complete theorem declarations. Exact canonical source multiplication/optimized square Montgomery word contracts and exact radix inverse derive mathematical field products. Symbolic count induction derives repeated-square field powers. Native compiler/caller, field inversion and full Transfer remain open. No ancestors replayed.'
replace(old,new)
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-field-values-checkpoint-20261012-01';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-extended-family-checkpoint-20261012-01/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_reports':4,'inherited_reports':1279,'owned_modules':160,'assembly_not_run':True})
