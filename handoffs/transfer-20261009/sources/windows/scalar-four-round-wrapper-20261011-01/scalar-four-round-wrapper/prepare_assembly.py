"""Seal source-extracted four-round carry wrapper and exact rejected predecessor."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-carry-schedule-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-carry-schedule-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-four-round-wrapper-20261011-02'")
s=s.replace('transfer-scalar-carry-schedule-checkpoint-20261011-02','transfer-scalar-four-round-wrapper-checkpoint-20261011-02').replace('scalar-carry-schedule-endpoint','scalar-four-round-wrapper-endpoint')
replace("MODULE = 'TransferScalarCarrySchedule01'", "MODULE = 'TransferScalarFourRoundWrapper01'")
replace('assert len(fresh) == 7','assert len(fresh) == 14')
replace("assert pool['objects'] == 80 and len(pool['inherited_public_reports']) == 756", "assert pool['objects'] == 81 and len(pool['inherited_public_reports']) == 763")
replace("manager_endpoint = DIAG / 'transfer-scalar-word-primitives-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-scalar-carry-schedule-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-word-primitives-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-carry-schedule-endpoint01.tar.xz'")
replace('897b85e4a0d9a638f6f6e9b8ac65ddf782608239496a90c1e496c54c2bd1e572','7483d5459b6bedc99fa4253f2e01c2f6c931c02d3f81369c8d234be454790755')
replace("tar.extractfile('reports/fresh-10-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 10','assert len(manager_reports) == 7')
replace("'module': 'TransferScalarWordPrimitives01'", "'module': 'TransferScalarCarrySchedule01'")
replace('assert len(combined_reports) == 756','assert len(combined_reports) == 763')
replace('assert len(manager_selected) == 80','assert len(manager_selected) == 81')
replace("reference = {'scalar_word_primitives':", "reference = {'scalar_carry_schedule':")
replace("'imported_complete_reports': 10", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 80, 'inherited_complete_reports': 756", "'complete_owned_modules': 81, 'inherited_complete_reports': 763")
s=s.replace('eighty-module','eighty-one-module').replace('756 original inherited','763 original inherited').replace('verified 756 inherited','verified 763 inherited')
replace("'fresh_definition_audits': 2", "'fresh_definition_audits': 5")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 9")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 14")
replace("'inherited_complete_public_audits': 756", "'inherited_complete_public_audits': 763")
replace("'fresh_audits': 7, 'inherited_audits': 756", "'fresh_audits': 14, 'inherited_audits': 763",2)
replace('SOURCE_SCALAR_SYMBOLIC_CARRY_SCHEDULE_AND_LOW_LIMB_QUOTIENT_QUALIFIED','SOURCE_SCALAR_FOUR_ROUND_FINITE_CARRY_WRAPPER_CANONICAL_RANGE_QUALIFIED')
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-14-complete-declarations.txt'")
start=s.index("failed=DIAG/'transfer-scalar-carry-schedule-20261011-01'");end=s.index("add(stdout, 'reports/fresh-14-complete-declarations.txt'",start)
s=s[:start]+'''failed=DIAG/'transfer-scalar-four-round-wrapper-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-association.json','handwritten/TransferScalarFourRoundWrapper01.lean','project/ShielddSecurity/TransferScalarFourRoundWrapper01.lean','runs/01-TransferScalarFourRoundWrapper01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/01/'+n,'two unfinished reflexive inequalities; all original raw diagnostics, zero proof/control credit')
''' + s[end:]
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
extra="\nrow = mapping['serializer_wrapper_source_association']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/serializer-wrapper-source-association.json', 'exact constants/zero-high-limbs/four rounds/final subtraction structure, no semantic or native credit')\n"
s=s.replace(anchor,anchor+extra,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Fourteen complete full type/axiom reports retained. Failed01 two unfinished reflexive inequalities retained with zero credit; fresh02 proof-only closure leaves all fourteen contracts/source constants unchanged. Actual model multipliers derived from current finite low words; recurrence and normalized canonical field range follow from the finite carry walk, with no input field-range or provided multiplier-vector premise. Pinned Rust zero-high-limb/ADC/sub/byte execution correspondence remains an interface. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':14,'inherited_reports':763,'owned_modules':81,'rejected_attempts':1})
