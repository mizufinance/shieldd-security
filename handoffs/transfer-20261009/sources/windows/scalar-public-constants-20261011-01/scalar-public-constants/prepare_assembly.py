from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-invert-chain-endpoint-20261011-05/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-invert-chain-20261011-05'","CURRENT = DIAG / 'transfer-scalar-public-constants-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-invert-chain-checkpoint-20261011-05'","CHECKPOINT = DIAG / 'transfer-scalar-public-constants-checkpoint-20261011-02'"),
 ("MODULE = 'TransferScalarInvertChain01'","MODULE = 'TransferScalarPublicConstants01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-invert-machine-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-scalar-invert-chain-endpoint-20261011-05'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-invert-machine-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-invert-chain-endpoint01.tar.xz'"),
 ('11cb4d8d14fba68ae139509e244ec879f116846d1b58452540b24d6fefa8dbd9','3fd2e29f3131ad794ce45b647a81155abf281a206aa2bfd99f1642b289d08c5e'),
 ("'module': 'TransferScalarInvertMachine01'","'module': 'TransferScalarInvertChain01'"),
 ("reference = {'scalar_invert_machine':","reference = {'scalar_invert_chain':"),
 ("assert len(fresh) == 12","assert len(fresh) == 6"),
 ("assert len(manager_reports) == 20","assert len(manager_reports) == 12"),
 ("manager_stdout = tar.extractfile('reports/fresh-20-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-12-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 6 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('inductive') == 1 and declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-scalar-invert-chain-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-public-constants-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-12-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")]:replace(a,b)
replace("CURRENT / ('generated/' + MODULE + '.lean')","CURRENT / ('handwritten/' + MODULE + '.lean')",2)
replace("for name in ['generate_source.py', 'prepare.py', 'prepare_recipe.py',","for name in ['prepare.py', 'prepare_recipe.py',")
s=s.replace('== 157','== 158').replace('== 1257','== 1269').replace('one-hundred-fifty-seven-module','one-hundred-fifty-eight-module').replace('1257 original inherited complete reports','1269 original inherited complete reports').replace('verified 1257 inherited reports','verified 1269 inherited reports')
start=s.index('for attempt in [1,2,3,4]:');end=s.index("row=mapping['scalar_invert_chain_source_shape']",start)
s=s[:start]+"""prior=DIAG/'transfer-scalar-public-constants-20261011-01'
names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-public-constants-shape.json','handwritten/TransferScalarPublicConstants01.lean','project/ShielddSecurity/TransferScalarPublicConstants01.lean']
assert not (prior/'runs/01-TransferScalarPublicConstants01/stdout.txt').exists()
for name in names:
    row=pin(prior/name)
    assert row in plan['pins']
    add(prior/name,'prior-public-constants-attempt01/'+name,'original physical pressure attempt;10 original raw artifacts, no module result, not a successful control')
row=mapping['scalar_public_constants_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-public-constants-shape.json','exact cached five public PrimeField literal/binding blocks checked against source words; static association only')
"""+s[end:]
start=s.index('oldAssemblyFourth=');end=s.index("review = {'status':",start);s=s[:start]+s[end:]
s=s.replace("'rejected_attempts': 4,","'rejected_attempts': 1,").replace('transfer-scalar-invert-chain-endpoint-v1','transfer-scalar-public-constants-endpoint-v1').replace('EXACT_SOURCE_INVERSION_CHAIN_CANONICAL_PAYLOAD_ZERO_REFUSAL_EXPONENT_INSTANCE_QUALIFIED','SOURCE_PUBLIC_SCALAR_CONSTANTS_CANONICAL_RAW_AND_SERIALIZATION_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete declarations:one inductive/two definitions/three theorems. Five original literals and public binding lines compared exactly to source. Derived raw bounds and canonical serialized keys, with stated closed Montgomery-value certificates. Original10 raw pressure-attempt artifacts retained; source/proofs/contracts/guards unchanged. Root orders/DELTA exponent/native/full Transfer remain open. No ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-public-constants-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-invert-chain-checkpoint-20261011-05/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1269,'owned_modules':158})
