"""Seal fixed-shift/cast ADC equations with unchanged source contracts and guards."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-four-round-wrapper-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-four-round-wrapper-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-adc-shift-20261011-02'")
s=s.replace('transfer-scalar-four-round-wrapper-checkpoint-20261011-02','transfer-scalar-adc-shift-checkpoint-20261011-02').replace('scalar-four-round-wrapper-endpoint','scalar-adc-shift-endpoint')
replace("MODULE = 'TransferScalarFourRoundWrapper01'", "MODULE = 'TransferScalarAdcShift01'")
replace('assert len(fresh) == 14','assert len(fresh) == 8')
replace("assert pool['objects'] == 81 and len(pool['inherited_public_reports']) == 763", "assert pool['objects'] == 82 and len(pool['inherited_public_reports']) == 777")
replace("manager_endpoint = DIAG / 'transfer-scalar-carry-schedule-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-four-round-wrapper-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-carry-schedule-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-four-round-wrapper-endpoint01.tar.xz'")
replace('7483d5459b6bedc99fa4253f2e01c2f6c931c02d3f81369c8d234be454790755','ff53e14b6f4e5b64c5b45888724c3e802c44d4e266bfaf739bd7477832151f06')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-14-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 14')
replace("'module': 'TransferScalarCarrySchedule01'", "'module': 'TransferScalarFourRoundWrapper01'")
replace('assert len(combined_reports) == 763','assert len(combined_reports) == 777')
replace('assert len(manager_selected) == 81','assert len(manager_selected) == 82')
replace("reference = {'scalar_carry_schedule':", "reference = {'scalar_four_round_wrapper':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 14")
replace("'complete_owned_modules': 81, 'inherited_complete_reports': 763", "'complete_owned_modules': 82, 'inherited_complete_reports': 777")
s=s.replace('eighty-one-module','eighty-two-module').replace('763 original inherited','777 original inherited').replace('verified 763 inherited','verified 777 inherited')
replace("'fresh_definition_audits': 5", "'fresh_definition_audits': 3")
replace("'fresh_theorem_audits': 9", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 14", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 763", "'inherited_complete_public_audits': 777")
replace("'fresh_audits': 14, 'inherited_audits': 763", "'fresh_audits': 8, 'inherited_audits': 777",2)
replace('SOURCE_SCALAR_FOUR_ROUND_FINITE_CARRY_WRAPPER_CANONICAL_RANGE_QUALIFIED','SOURCE_SCALAR_FIXED_HIGH_SHIFT_CAST_AND_ZERO_UPPER_ADC_QUALIFIED')
replace("add(stdout, 'reports/fresh-14-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
start=s.index("failed=DIAG/'transfer-scalar-four-round-wrapper-20261011-01'");end=s.index("add(stdout, 'reports/fresh-8-complete-declarations.txt'",start)
s=s[:start]+'''failed=DIAG/'transfer-scalar-adc-shift-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarAdcShift01.lean','project/ShielddSecurity/TransferScalarAdcShift01.lean','runs/01-TransferScalarAdcShift01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/01/'+n,'radix reflexivity/BitVec one notation errors; original full raw diagnostics, zero proof/control credit')
''' + s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. Failed01 radix reflexivity and width-indexed BitVec one notation mismatch diagnostics retained with zero credit; fresh02 proof-only repairs leave all eight declaration contracts unchanged. Source-shaped shift/cast and ADC model equations and zero-high-limb carry conservation proved; actual Rust primitive/trace/SBB/endian correspondence remains an interface. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':777,'owned_modules':82,'rejected_attempts':1})
