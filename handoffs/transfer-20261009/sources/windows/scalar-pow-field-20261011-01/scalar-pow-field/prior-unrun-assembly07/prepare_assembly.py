from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-pow-bit-integer-endpoint-20261012-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-pow-bit-integer-20261012-03'","CURRENT = DIAG / 'transfer-scalar-pow-field-20261012-07'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-pow-bit-integer-checkpoint-20261012-03'","CHECKPOINT = DIAG / 'transfer-scalar-pow-field-checkpoint-20261012-07'"),
 ("MODULE = 'TransferScalarPowBitInteger01'","MODULE = 'TransferScalarPowField01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-invert-field-endpoint-20261012-03'","manager_endpoint = DIAG / 'transfer-scalar-pow-bit-integer-endpoint-20261012-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-invert-field-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-pow-bit-integer-endpoint01.tar.xz'"),
 ('f2b15f75a23678c33590aad11df4c302a79575628dcc34ccc05adbcd5843db1e','32b7290c2eed3d3501e7824a6a8ef647d55d967fd9bffee4620d27f5501973c3'),
 ("'module': 'TransferScalarInvertField01'","'module': 'TransferScalarPowBitInteger01'"),
 ("reference = {'scalar_invert_field':","reference = {'scalar_pow_bit_integer':"),
 ('assert len(manager_reports) == 7','assert len(manager_reports) == 6'),
 ("manager_stdout = tar.extractfile('reports/fresh-7-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("archive = ROOT / 'portable-windows-scalar-pow-bit-integer-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-pow-field-endpoint01.tar.xz'")]:replace(a,b)
s=s.replace('== 162','== 163').replace('== 1290','== 1296').replace('one-hundred-sixty-two-module','one-hundred-sixty-three-module').replace('1290 original inherited complete reports','1296 original inherited complete reports').replace('verified 1290 inherited reports','verified 1296 inherited reports')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['scalar_invert_field_source_shape']",start)
history="""for attempt in [1,2,3,4,5,6]:
    prior=DIAG/('transfer-scalar-pow-field-20261012-%02d'%attempt)
    names=['prepare_recipe.py','prepare.py','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
    if attempt==6:assert not (prior/'plan.json').exists()
    else:names+=['plan.json','review.json']
    if attempt in [1,3,5,6]:assert not (prior/'events.jsonl').exists()
    else:
        names.append('events.jsonl')
        priorStdout=prior/'runs/01-TransferScalarPowField01/stdout.txt'
        if attempt==2:
            assert priorStdout.exists();names.append('runs/01-TransferScalarPowField01/stdout.txt')
        else:assert not priorStdout.exists()
    for name in names:
        row=pin(prior/name);assert row in plan['pins']
        add(prior/name,'prior-power-attempt%02d/'%attempt+name,'original unrun predecessor/warning rejection/physical-pressure stop/setup omission; every actual raw file retained unchanged')
priorComposition=DIAG/'transfer-scalar-pow-field-owned-floor-20261012-06/composition-review.json'
assert pin(priorComposition) in plan['pins']
add(priorComposition,'prior-power-attempt06/composition-review.json','original prepared dependency composition before stale metadata key stopped setup; no execution')
for key,filename in [('scalar_pow_field_source_shape','scalar-pow-field-shape.json'),('scalar_pow_bit_integer_source_shape','scalar-pow-bit-integer-shape.json')]:
    row=mapping[key];assert pin(row['path'])==row and row in plan['pins']
    add(row['path'],'context/'+filename,'exact field operation/word exponent source identities; actual modeled power, native binding separate')
"""
s=s[:start]+history+s[end:]
start=s.index("    'scope': mapping['scope'] + '");end=s.index("}\ndump(ROOT / 'review.json'",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete theorem declarations derive bit/word field exponents and final constant/variable source pow from the exact ONE initial value and reconstructed exponent integer. Two unused simp arguments removed, direct import narrowed to required field operations, and only complete actual word dependency branch selected; theorem statements and every execution guard unchanged. Original56 prior raw producer/composition artifacts retained, including full warning rejection and pressure-stop events with absent pressure stdout. Independently qualified inverse/prime packet retained separately; no ancestors replayed. Native compiler/Choice/caller/full Transfer remain open.'"+s[end:]
s=s.replace("'status': 'SOURCE_PUBLIC_SCALAR_CONSTANTS_CANONICAL_RAW_AND_SERIALIZATION_QUALIFIED'","'status': 'SOURCE_SCALAR_POWER_EXACT_MATHEMATICAL_FIELD_VALUE_QUALIFIED'")
s=s.replace("'rejected_attempts': 1, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0","'rejected_attempts': 2, 'withdrawn_unrun_sources': 3, 'unprepared_setup_failures': 1")
at=s.index("add(Path(__file__), 'assemble.py'")
extra="""for endpoint,names in [(3,['prepare_assembly.py']),(4,['prepare_recipe_from03.py','prepare_assembly.py','assemble.py']),(5,['prepare_assembly.py','assemble.py']),(6,['prepare_assembly.py','assemble.py'])]:
    priorEndpoint=DIAG/('transfer-scalar-pow-field-endpoint-20261012-%02d'%endpoint)
    assert not (priorEndpoint/'manifest.json').exists()
    for name in names:add(priorEndpoint/name,'prior-unrun-assembly%02d/'%endpoint+name,'original failed setup/unrun assembly derivation preserved unchanged; no sealed prior result')
"""
s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-pow-field-checkpoint-20261012-07';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'whole_owned_modules':163,'inherited_complete_reports':1296,'fresh_theorems':6,'prior_raw_artifacts':56,'all_guards_unchanged':True,'assembly_not_run':True})
