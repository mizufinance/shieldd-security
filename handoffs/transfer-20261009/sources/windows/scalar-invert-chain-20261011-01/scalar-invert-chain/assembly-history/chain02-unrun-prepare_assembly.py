from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-invert-machine-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-invert-machine-20261011-01'","CURRENT = DIAG / 'transfer-scalar-invert-chain-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-invert-machine-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-scalar-invert-chain-checkpoint-20261011-02'"),
 ("MODULE = 'TransferScalarInvertMachine01'","MODULE = 'TransferScalarInvertChain01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-pow-invariant-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-scalar-invert-machine-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-pow-invariant-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-invert-machine-endpoint01.tar.xz'"),
 ('a931f28536968c8fcaa746a26d696216e663432e303178439f92dddd22b83687','11cb4d8d14fba68ae139509e244ec879f116846d1b58452540b24d6fefa8dbd9'),
 ("'module': 'TransferScalarPowInvariant01'","'module': 'TransferScalarInvertMachine01'"),
 ("reference = {'scalar_pow_invariant':","reference = {'scalar_invert_machine':"),
 ("assert len(fresh) == 20","assert len(fresh) == 9"),
 ("assert len(manager_reports) == 15","assert len(manager_reports) == 20"),
 ("manager_stdout = tar.extractfile('reports/fresh-15-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-20-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 14 and declaration_kinds.count('inductive') == 2 and declaration_kinds.count('theorem') == 4","assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 6"),
 ("archive = ROOT / 'portable-windows-scalar-invert-machine-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-invert-chain-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-20-complete-declarations.txt'","add(stdout, 'reports/fresh-9-complete-declarations.txt'")]:replace(a,b)
replace("CURRENT / ('handwritten/' + MODULE + '.lean')","CURRENT / ('generated/' + MODULE + '.lean')",2)
replace("for name in ['prepare.py', 'prepare_recipe.py',","for name in ['generate_source.py', 'prepare.py', 'prepare_recipe.py',")
s=s.replace('== 156','== 157').replace('== 1237','== 1257').replace('one-hundred-fifty-six-module','one-hundred-fifty-seven-module').replace('1237 original inherited complete reports','1257 original inherited complete reports').replace('verified 1237 inherited reports','verified 1257 inherited reports')
replace("row=mapping['scalar_invert_machine_source_shape']","""prior=DIAG/'transfer-scalar-invert-chain-20261011-01'
names=['generate_source.py','prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-chain-shape.json','generated/TransferScalarInvertChain01.lean','project/ShielddSecurity/TransferScalarInvertChain01.lean']
assert not (prior/'runs/01-TransferScalarInvertChain01/stdout.txt').exists()
for name in names:
    row=pin(prior/name)
    assert row in plan['pins']
    add(prior/name,'prior-invert-chain-attempt01/'+name,'original physical pressure attempt;11 original raw artifacts, no Lean stdout/module result, not a successful control')
row=mapping['scalar_invert_chain_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-invert-chain-shape.json','exact cached source85 ordered statements/initialized register parsing/finite exponent crosscheck; generator source preserved; static source association separate from field inverse and native compiler/caller proof')
row=mapping['scalar_invert_machine_source_shape']""")
s=s.replace("'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0").replace('transfer-scalar-invert-machine-endpoint-v1','transfer-scalar-invert-chain-endpoint-v1').replace('SYMBOLIC_INVERSION_REGISTER_MACHINE_INITIALIZED_READS_QUALIFIED','EXACT_SOURCE_INVERSION_CHAIN_CANONICAL_PAYLOAD_ZERO_REFUSAL_EXPONENT_INSTANCE_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Nine complete declarations:three definitions/six theorems. Generated exact85 statement instance has all reads initialized, canonical payload, exact modeled zero refusal and independent natural exponent p-2 certificate. Original11 pressure-attempt raw artifacts retained; identical source regenerated only through identical generator. Field exponent/inverse/native/full Transfer remain open. No ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-invert-chain-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-invert-machine-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':9,'inherited_reports':1257,'owned_modules':157,'generated_source_and_generator_preserved':True})
