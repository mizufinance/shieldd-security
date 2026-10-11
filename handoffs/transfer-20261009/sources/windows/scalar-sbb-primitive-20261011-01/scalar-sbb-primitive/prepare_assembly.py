"""Seal source-shaped single-word SBB and exact proof-only conditional repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-adc-shift-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-adc-shift-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-sbb-primitive-20261011-02'")
s=s.replace('transfer-scalar-adc-shift-checkpoint-20261011-02','transfer-scalar-sbb-primitive-checkpoint-20261011-02').replace('scalar-adc-shift-endpoint','scalar-sbb-primitive-endpoint')
replace("MODULE = 'TransferScalarAdcShift01'", "MODULE = 'TransferScalarSbbPrimitive01'")
replace('assert len(fresh) == 8','assert len(fresh) == 9')
replace("assert pool['objects'] == 82 and len(pool['inherited_public_reports']) == 777", "assert pool['objects'] == 83 and len(pool['inherited_public_reports']) == 785")
replace("manager_endpoint = DIAG / 'transfer-scalar-four-round-wrapper-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-adc-shift-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-four-round-wrapper-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-adc-shift-endpoint01.tar.xz'")
replace('ff53e14b6f4e5b64c5b45888724c3e802c44d4e266bfaf739bd7477832151f06','f8109d3e4a3ac224848f165ef605064e60bd946d1f356d59fa813134a40faf2d')
replace("tar.extractfile('reports/fresh-14-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 14','assert len(manager_reports) == 8')
replace("'module': 'TransferScalarFourRoundWrapper01'", "'module': 'TransferScalarAdcShift01'")
replace('assert len(combined_reports) == 777','assert len(combined_reports) == 785')
replace('assert len(manager_selected) == 82','assert len(manager_selected) == 83')
replace("reference = {'scalar_four_round_wrapper':", "reference = {'scalar_adc_shift':")
replace("'imported_complete_reports': 14", "'imported_complete_reports': 8")
replace("'complete_owned_modules': 82, 'inherited_complete_reports': 777", "'complete_owned_modules': 83, 'inherited_complete_reports': 785")
s=s.replace('eighty-two-module','eighty-three-module').replace('777 original inherited','785 original inherited').replace('verified 777 inherited','verified 785 inherited')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 4")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 9")
replace("'inherited_complete_public_audits': 777", "'inherited_complete_public_audits': 785")
replace("'fresh_audits': 8, 'inherited_audits': 777", "'fresh_audits': 9, 'inherited_audits': 785",2)
replace('SOURCE_SCALAR_FIXED_HIGH_SHIFT_CAST_AND_ZERO_UPPER_ADC_QUALIFIED','SOURCE_SCALAR_REACHABLE_BORROW_MASK_SBB_SINGLE_WORD_ARITHMETIC_QUALIFIED')
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-9-complete-declarations.txt'")
start=s.index("failed=DIAG/'transfer-scalar-adc-shift-20261011-01'");end=s.index("add(stdout, 'reports/fresh-9-complete-declarations.txt'",start)
s=s[:start]+'''failed=DIAG/'transfer-scalar-sbb-primitive-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSbbPrimitive01.lean','project/ShielddSecurity/TransferScalarSbbPrimitive01.lean','runs/01-TransferScalarSbbPrimitive01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/01/'+n,'two unreduced low-word conditionals; original full raw diagnostics, zero proof/control credit')
''' + s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Nine complete full type/axiom reports retained. Failed01 two unreduced low-word conditionals retained with zero credit; fresh02 proof-only branch reduction leaves all nine declaration contracts unchanged. Widened wrapping subtraction, exact outgoing borrow masks and low-word conservation proved for reachable zero/all-ones input masks. Actual Rust primitive/trace/whole limb sub/add-back/endian correspondence remains an interface. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':9,'inherited_reports':785,'owned_modules':83,'rejected_attempts':1})
