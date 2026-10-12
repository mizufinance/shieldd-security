from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-field-values-endpoint-20261012-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-field-values-20261012-01'","CURRENT = DIAG / 'transfer-scalar-invert-field-20261012-03'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-field-values-checkpoint-20261012-01'","CHECKPOINT = DIAG / 'transfer-scalar-invert-field-checkpoint-20261012-03'"),
 ("MODULE = 'TransferScalarFieldValues01'","MODULE = 'TransferScalarInvertField01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-extended-family-endpoint-20261012-01'","manager_endpoint = DIAG / 'transfer-scalar-field-values-endpoint-20261012-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-extended-family-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-field-values-endpoint01.tar.xz'"),
 ('68d7ab736e5e02c82a8e2bacb2a092edbfa2f3888e465434b1002d10d7b77448','154f551c0d7c0a32e08f126acaf931b05ed097af7287e9205da07f6ffe3f1a38'),
 ("'module': 'TransferScalarExtendedFamily01'","'module': 'TransferScalarFieldValues01'"),
 ("reference = {'scalar_extended_family':","reference = {'scalar_field_values':"),
 ('assert len(fresh) == 4','assert len(fresh) == 7'),
 ("assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 4","assert declaration_kinds.count('inductive') == 0 and declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 6"),
 ("archive = ROOT / 'portable-windows-scalar-field-values-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-7-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 160','== 161').replace('== 1279','== 1283').replace('one-hundred-sixty-module','one-hundred-sixty-one-module').replace('1279 original inherited complete reports','1283 original inherited complete reports').replace('verified 1279 inherited reports','verified 1283 inherited reports')
marker="row=mapping['scalar_field_values_source_shape']"
extra="""for attempt in [1,2]:
    prior=DIAG/('transfer-scalar-invert-field-20261012-%02d'%attempt)
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-invert-field-shape.json','handwritten/TransferScalarInvertField01.lean','project/ShielddSecurity/TransferScalarInvertField01.lean']
    prior_stdout=prior/'runs/01-TransferScalarInvertField01/stdout.txt'
    if attempt==1: assert not prior_stdout.exists()
    else:
        assert prior_stdout.exists()
        names.append('runs/01-TransferScalarInvertField01/stdout.txt')
    for name in names:
        row=pin(prior/name);assert row in plan['pins']
        add(prior/name,'prior-invert-field-attempt%02d/'%attempt+name,'original failed physical-pressure/proof-script attempt; all original raw source/plans/events/full written stdout retained, no qualified result')
row=mapping['scalar_invert_field_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-invert-field-shape.json','exact qualified word machine/source instance/mathematical operation sources; symbolic field exponent simulation, Fermat/native caller separate')
"""
replace(marker,extra+marker)
old=' Four complete theorem declarations. Exact canonical source multiplication/optimized square Montgomery word contracts and exact radix inverse derive mathematical field products. Symbolic count induction derives repeated-square field powers. Native compiler/caller, field inversion and full Transfer remain open. No ancestors replayed.'
new=' Seven complete declarations:one definition/six theorems. Symbolic operand/register/step/walk correspondence derives exact source85-statement inversion payload field value input^(p-2) modulo p. Original21 raw failed-attempt artifacts retained, including full failed Lean output. Only two proof-script lines repaired; source algorithm/conclusions/contracts/guards unchanged. Fermat/field inversion and native compiler/caller/full Transfer remain open. No ancestors replayed.'
replace(old,new)
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-invert-field-checkpoint-20261012-03';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-field-values-checkpoint-20261012-01/preservation_check.py',checkpoint/'preservation_check.py')
print({'fresh_reports':7,'inherited_reports':1283,'owned_modules':161,'prior_failed_raw_artifacts':21,'assembly_not_run':True})
