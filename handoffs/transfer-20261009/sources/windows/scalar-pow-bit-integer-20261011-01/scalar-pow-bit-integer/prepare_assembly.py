from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-invert-field-endpoint-20261012-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-invert-field-20261012-03'","CURRENT = DIAG / 'transfer-scalar-pow-bit-integer-20261012-03'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-invert-field-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-pow-bit-integer-checkpoint-20261012-03'"),
 ("MODULE = 'TransferScalarInvertField01'","MODULE = 'TransferScalarPowBitInteger01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-field-values-endpoint-20261012-01'","manager_endpoint = DIAG / 'transfer-scalar-invert-field-endpoint-20261012-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-field-values-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'"),
 ('154f551c0d7c0a32e08f126acaf931b05ed097af7287e9205da07f6ffe3f1a38','f2b15f75a23678c33590aad11df4c302a79575628dcc34ccc05adbcd5843db1e'),
 ("'module': 'TransferScalarFieldValues01'","'module': 'TransferScalarInvertField01'"),
 ("reference = {'scalar_field_values':","reference = {'scalar_invert_field':"),
 ('assert len(fresh) == 7','assert len(fresh) == 6'),
 ('assert len(manager_reports) == 4','assert len(manager_reports) == 7'),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')"),
 ("assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 6","assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 6"),
 ("archive = ROOT / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-pow-bit-integer-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-7-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 161','== 162').replace('== 1283','== 1290').replace('one-hundred-sixty-one-module','one-hundred-sixty-two-module').replace('1283 original inherited complete reports','1290 original inherited complete reports').replace('verified 1283 inherited reports','verified 1290 inherited reports')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['scalar_invert_field_source_shape']",start)
extra="""for attempt in [1,2]:
    prior=DIAG/('transfer-scalar-pow-bit-integer-20261012-%02d'%attempt)
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-pow-bit-integer-shape.json','handwritten/TransferScalarPowBitInteger01.lean','project/ShielddSecurity/TransferScalarPowBitInteger01.lean']
    prior_stdout=prior/'runs/01-TransferScalarPowBitInteger01/stdout.txt'
    if attempt==2: assert not prior_stdout.exists()
    else:
        assert prior_stdout.exists()
        names.append('runs/01-TransferScalarPowBitInteger01/stdout.txt')
    for name in names:
        row=pin(prior/name);assert row in plan['pins']
        add(prior/name,'prior-pow-bit-attempt%02d/'%attempt+name,'original failed proof-script/physical-pressure attempt; all original raw source/plans/events/full written stdout retained, no qualified result')
row=mapping['scalar_pow_bit_integer_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-pow-bit-integer-shape.json','exact power model/official UInt bitwise/Nat modular source identities; symbolic binary reconstruction, native binding separate')
"""
s=s[:start]+extra+s[end:]
old=' Seven complete declarations:one definition/six theorems. Symbolic operand/register/step/walk correspondence derives exact source85-statement inversion payload field value input^(p-2) modulo p. Original21 raw failed-attempt artifacts retained, including full failed Lean output. Only two proof-script lines repaired; source algorithm/conclusions/contracts/guards unchanged. Fermat/field inversion and native compiler/caller/full Transfer remain open. No ancestors replayed.'
new=' Six complete theorem declarations. Actual modeled bounded UInt64 bit shift/mask/Boolean digit and symbolic count/member/list recurrence derive exact64-bit word and arbitrary reversed-word little-endian exponent integer. Original21 raw failed-attempt artifacts retained, including full failed Lean output. One beta simplification repaired; source algorithm/conclusions/contracts/guards unchanged. Field-power fold and native compiler/caller/full Transfer remain open. No ancestors replayed.'
replace(old,new)
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-bit-integer-checkpoint-20261012-03';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-invert-field-checkpoint-20261012-03/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_reports':6,'inherited_reports':1290,'owned_modules':162,'prior_failed_raw_artifacts':21,'assembly_not_run':True})
