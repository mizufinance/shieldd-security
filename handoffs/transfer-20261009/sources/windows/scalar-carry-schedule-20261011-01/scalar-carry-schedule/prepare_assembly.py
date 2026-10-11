"""Seal exact symbolic carry schedule and unchanged-contract proof repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-word-primitives-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-word-primitives-20261011-03'", "CURRENT = DIAG / 'transfer-scalar-carry-schedule-20261011-02'")
s=s.replace('transfer-scalar-word-primitives-checkpoint-20261011-03','transfer-scalar-carry-schedule-checkpoint-20261011-02').replace('scalar-word-primitives-endpoint','scalar-carry-schedule-endpoint')
replace("MODULE = 'TransferScalarWordPrimitives01'", "MODULE = 'TransferScalarCarrySchedule01'")
replace('assert len(fresh) == 10','assert len(fresh) == 7')
replace("assert pool['objects'] == 79 and len(pool['inherited_public_reports']) == 746", "assert pool['objects'] == 80 and len(pool['inherited_public_reports']) == 756")
replace("manager_endpoint = DIAG / 'transfer-scalar-serialization-range-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-word-primitives-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-serialization-range-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-word-primitives-endpoint01.tar.xz'")
replace('1f9989bc6e820940f86b249da9c120fedc9383203a083b2f2debffcee57bfda8','897b85e4a0d9a638f6f6e9b8ac65ddf782608239496a90c1e496c54c2bd1e572')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-10-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 10')
replace("'module': 'TransferScalarSerializationRange01'", "'module': 'TransferScalarWordPrimitives01'")
replace('assert len(combined_reports) == 746','assert len(combined_reports) == 756')
replace('assert len(manager_selected) == 79','assert len(manager_selected) == 80')
replace("reference = {'scalar_serialization_range':", "reference = {'scalar_word_primitives':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 10")
replace("'complete_owned_modules': 79, 'inherited_complete_reports': 746", "'complete_owned_modules': 80, 'inherited_complete_reports': 756")
s=s.replace('seventy-nine-module','eighty-module').replace('746 original inherited','756 original inherited').replace('verified 746 inherited','verified 756 inherited')
replace("'fresh_definition_audits': 4", "'fresh_definition_audits': 2")
replace("'fresh_theorem_audits': 6", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 10", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 746", "'inherited_complete_public_audits': 756")
replace("'fresh_audits': 10, 'inherited_audits': 746", "'fresh_audits': 7, 'inherited_audits': 756",2)
replace('SOURCE_SCALAR_FINITE_U64_INPUTS_AND_WIDENED_MAC_ARITHMETIC_QUALIFIED','SOURCE_SCALAR_SYMBOLIC_CARRY_SCHEDULE_AND_LOW_LIMB_QUOTIENT_QUALIFIED')
replace("add(stdout, 'reports/fresh-10-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
start=s.index("failed=DIAG/'transfer-scalar-word-primitives-20261011-02'");end=s.index("add(stdout, 'reports/fresh-7-complete-declarations.txt'",start)
s=s[:start]+'''failed=DIAG/'transfer-scalar-carry-schedule-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCarrySchedule01.lean','project/ShielddSecurity/TransferScalarCarrySchedule01.lean','runs/01-TransferScalarCarrySchedule01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/01/'+n,'failed original radix rewrite and nonexistent List lemma diagnostics; zero proof/control credit')
''' + s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. Failed01 radix rewrite and nonexistent List lemma diagnostics retained with zero credit; fresh02 proof-only repair leaves all seven declaration contracts unchanged. Generic finite MAC loop conservation and exact low-word quotient proved, not native Rust trace/ADC/SBB/four-round wrapper/byte layout closure. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':756,'owned_modules':80,'rejected_attempts':1})
