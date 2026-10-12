from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-public-constants-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-public-constants-20261011-02'","CURRENT = DIAG / 'transfer-scalar-extended-family-20261012-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-public-constants-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-extended-family-checkpoint-20261012-01'"),
 ("MODULE = 'TransferScalarPublicConstants01'","MODULE = 'TransferScalarExtendedFamily01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-invert-chain-endpoint-20261011-05'","manager_endpoint = DIAG / 'transfer-scalar-public-constants-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-invert-chain-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-public-constants-endpoint01.tar.xz'"),
 ('3fd2e29f3131ad794ce45b647a81155abf281a206aa2bfd99f1642b289d08c5e','86fe9931d47919832ca078095ff47f6bae52162b279b66dfaab6d6a7c3d04989'),
 ("'module': 'TransferScalarInvertChain01'","'module': 'TransferScalarPublicConstants01'"),
 ("reference = {'scalar_invert_chain':","reference = {'scalar_public_constants':"),
 ('assert len(fresh) == 6','assert len(fresh) == 4'),
 ('assert len(manager_reports) == 12','assert len(manager_reports) == 6'),
 ("manager_stdout = tar.extractfile('reports/fresh-12-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("assert declaration_kinds.count('inductive') == 1 and declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('inductive') == 1 and declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 2"),
 ("archive = ROOT / 'portable-windows-scalar-public-constants-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-extended-family-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 158','== 159').replace('== 1269','== 1275').replace('one-hundred-fifty-eight-module','one-hundred-fifty-nine-module').replace('1269 original inherited complete reports','1275 original inherited complete reports').replace('verified 1269 inherited reports','verified 1275 inherited reports')
start=s.index("prior=DIAG/'transfer-scalar-public-constants-20261011-01'");end=s.index("row=mapping['scalar_public_constants_source_shape']",start)
s=s[:start]+s[end:]
marker="row=mapping['scalar_public_constants_source_shape']"
replace(marker,"row=mapping['scalar_extended_family_source_shape']\nassert pin(row['path'])==row and row in plan['pins']\nadd(row['path'],'context/scalar-extended-family-shape.json','exact cached u64/random64-byte/conditional selection source bodies and explicit represented/excluded constructor inventory; static association only')\n"+marker)
old=' Six complete declarations:one inductive/two definitions/three theorems. Five original literals and public binding lines compared exactly to source. Derived raw bounds and canonical serialized keys, with stated closed Montgomery-value certificates. Original10 raw pressure-attempt artifacts retained; source/proofs/contracts/guards unchanged. Root orders/DELTA exponent/native/full Transfer remain open. No ancestors replayed.'
new=' Four complete declarations:one inductive/one definition/two theorems. Every successfully constructed represented program derives canonical raw fields and exact32-byte key; inversion refusal derives earlier construction failure or exact source zero payload. Explicit source API constructor inventory and exclusions retained. Native Choice/RNG/ct_eq/compiler/caller/helper trace, field exponent/inverse and full Transfer remain open. No ancestors replayed.'
replace(old,new)
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-extended-family-checkpoint-20261012-01';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-public-constants-checkpoint-20261011-02/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_reports':4,'inherited_reports':1275,'owned_modules':159,'assembly_not_run':True})
