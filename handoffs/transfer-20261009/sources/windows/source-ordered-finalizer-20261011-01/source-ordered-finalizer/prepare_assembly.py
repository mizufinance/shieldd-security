"""Seal fresh source-order correction with setup and pressure refusals retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-canonical-word-equality-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-canonical-word-equality-20261011-02'", "CURRENT = DIAG / 'transfer-source-ordered-finalizer-20261011-03'")
s=s.replace('transfer-canonical-word-equality-checkpoint-20261011-02','transfer-source-ordered-finalizer-checkpoint-20261011-03').replace('canonical-word-equality-endpoint','source-ordered-finalizer-endpoint')
replace("MODULE = 'TransferCanonicalWordEquality01'", "MODULE = 'TransferSourceOrderedFinalizer01'")
replace('assert len(fresh) == 6','assert len(fresh) == 7')
replace("assert pool['objects'] == 101 and len(pool['inherited_public_reports']) == 911", "assert pool['objects'] == 102 and len(pool['inherited_public_reports']) == 917")
replace("manager_endpoint = DIAG / 'transfer-complete-block-driver-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-canonical-word-equality-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-complete-block-driver-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-canonical-word-equality-endpoint01.tar.xz'")
replace('351f336d80a662de1e1abbbe37f0584d2cad5bc54f3d3e379c753c2915bacc22','3e27ae27d4a807a69d112534e53a74f6bcb8decf57ab16b3423365623c97183f')
replace("tar.extractfile('reports/fresh-2-complete-declarations.txt')", "tar.extractfile('reports/fresh-6-complete-declarations.txt')")
replace('assert len(manager_reports) == 2','assert len(manager_reports) == 6')
replace("'module': 'TransferCompleteBlockDriver01'", "'module': 'TransferCanonicalWordEquality01'")
replace('assert len(combined_reports) == 911','assert len(combined_reports) == 917')
replace('assert len(manager_selected) == 101','assert len(manager_selected) == 102')
replace("reference = {'complete_block_driver':", "reference = {'canonical_word_equality':")
replace("'imported_complete_reports': 2", "'imported_complete_reports': 6")
replace("'complete_owned_modules': 101, 'inherited_complete_reports': 911", "'complete_owned_modules': 102, 'inherited_complete_reports': 917")
s=s.replace('one-hundred-one-module','one-hundred-two-module').replace('911 original inherited','917 original inherited').replace('verified 911 inherited','verified 917 inherited')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 3")
replace("'fresh_structure_audits': 1", "'fresh_structure_audits': 0")
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 911", "'inherited_complete_public_audits': 917")
replace("'fresh_audits': 6, 'inherited_audits': 911", "'fresh_audits': 7, 'inherited_audits': 917",2)
replace("'rejected_attempts': 1", "'rejected_attempts': 2")
s=s.replace('SOURCE_CANONICAL_INTERNAL_WORD_MATH_BYTE_EQUALITY_QUALIFIED','SOURCE_CORRECTED_KNOWN_FINALIZATION_ORDER_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-6-complete-declarations.txt'",start)
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact corrected known source-order recipe; finite guards unchanged')
failed=DIAG/'transfer-source-ordered-finalizer-20261011-02'
for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/corrected-finalization-call-order.json','handwritten/TransferSourceOrderedFinalizer01.lean','project/ShielddSecurity/TransferSourceOrderedFinalizer01.lean','runs/01-TransferSourceOrderedFinalizer01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected-pressure/02/'+n,'physical pressure stop; no proof/control credit')
assert (failed/'handwritten/TransferSourceOrderedFinalizer01.lean').read_bytes()==(CURRENT/'handwritten/TransferSourceOrderedFinalizer01.lean').read_bytes()
failedSetup=DIAG/'transfer-source-ordered-finalizer-20261011-01/prepare_recipe.py'
assert pin(failedSetup) in plan['pins']
add(failedSetup,'rejected-setup/01/prepare_recipe.py','setup confused old inventory order with call order; no plan or kernel invocation; zero credit')
"""
s=s[:start]+extra+s[end:]
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
at=s.index("row = mapping['fixed_finalization_source_association']")
s=s[:at]+"row = mapping['corrected_finalization_source_order']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/corrected-finalization-call-order.json', 'fresh reordered inventory follows authenticated source call positions; static association only')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. Failed01 setup recipe retained, no kernel invocation; pressure02 full raw retained, zero credit; fresh03 identical handwritten source and finite guards. Corrected known mutation order agrees with authenticated pinned source call positions. Original fixed list remains immutable and valid only as its defined model, no native source order claim. Native full trace/hidden callee/value/primitive/field/cache/snapshot/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('canonical internal raw word equality iff mathematical Montgomery value equality iff source serialized byte equality','known SCT/compliance/routing mutation order corrected in fresh typed source publication')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':917,'owned_modules':102,'rejected_setup':1,'rejected_pressure':1})
