"""Seal exact source serializer reversed-byte ordering, rejected singleton attempts raw."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-source-ordered-driver-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-source-ordered-driver-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-reversed-byte-order-20261011-03'")
s=s.replace('transfer-source-ordered-driver-checkpoint-20261011-01','transfer-scalar-reversed-byte-order-checkpoint-20261011-03').replace('source-ordered-driver-endpoint','scalar-reversed-byte-order-endpoint')
replace("MODULE = 'TransferSourceOrderedDriver01'", "MODULE = 'TransferScalarReversedByteOrder01'")
replace('assert len(fresh) == 4','assert len(fresh) == 8')
replace("assert pool['objects'] == 103 and len(pool['inherited_public_reports']) == 924", "assert pool['objects'] == 104 and len(pool['inherited_public_reports']) == 928")
replace("manager_endpoint = DIAG / 'transfer-source-ordered-finalizer-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-source-ordered-driver-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-source-ordered-finalizer-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-source-ordered-driver-endpoint01.tar.xz'")
replace('ea9ffe003d90a1bcd4e16b2fb784df0abab224530042ae04a53ca05c4f98a18b','0f935506e34cb366ab5e08abc1cce3827dc8809127fdb613e727d67361187eec')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-4-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 4')
replace("'module': 'TransferSourceOrderedFinalizer01'", "'module': 'TransferSourceOrderedDriver01'")
replace('assert len(combined_reports) == 924','assert len(combined_reports) == 928')
replace('assert len(manager_selected) == 103','assert len(manager_selected) == 104')
replace("reference = {'source_ordered_finalizer':", "reference = {'source_ordered_driver':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 103, 'inherited_complete_reports': 924", "'complete_owned_modules': 104, 'inherited_complete_reports': 928")
s=s.replace('one-hundred-three-module','one-hundred-four-module').replace('924 original inherited','928 original inherited').replace('verified 924 inherited','verified 928 inherited')
replace("'fresh_definition_audits': 2", "'fresh_definition_audits': 1")
replace("'fresh_theorem_audits': 2", "'fresh_theorem_audits': 7")
replace("'fresh_complete_public_audits': 4", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 924", "'inherited_complete_public_audits': 928")
replace("'fresh_audits': 4, 'inherited_audits': 924", "'fresh_audits': 8, 'inherited_audits': 928",2)
replace("'rejected_attempts': 0", "'rejected_attempts': 2")
s=s.replace('SOURCE_CORRECTED_RETURNED_BLOCK_DRIVER_PUBLICATION_QUALIFIED','SOURCE_TYPED_REVERSED_BYTE_SCALAR_ORDER_QUALIFIED')
at=s.index("add(stdout, 'reports/fresh-4-complete-declarations.txt'")
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact exposed singleton recursion/case repair; finite guards unchanged')
for attempt in ['01','02']:
    failed=DIAG/('transfer-scalar-reversed-byte-order-20261011-'+attempt)
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarReversedByteOrder01.lean','project/ShielddSecurity/TransferScalarReversedByteOrder01.lean','runs/01-TransferScalarReversedByteOrder01/stdout.txt']
    if attempt=='02':names.append('recipe_source.py')
    for n in names:
        assert pin(failed/n) in plan['pins']
        add(failed/n,'rejected-kernel/'+attempt+'/'+n,'singleton lexicographic match compiler failure; zero proof/control credit')
failed=DIAG/'transfer-scalar-reversed-byte-order-20261011-01'
old=(failed/'handwritten/TransferScalarReversedByteOrder01.lean').read_text()
assert old.count('    | nil => rfl')==2
old=old.replace('    | nil => rfl','    | nil => simp only [List.nil_append, compareHighFirst]; cases compare lastLeft.toNat lastRight.toNat <;> rfl',1)
assert old==(CURRENT/'handwritten/TransferScalarReversedByteOrder01.lean').read_text()
"""
s=s[:at]+extra+s[at:]
replace("add(stdout, 'reports/fresh-4-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. Failed01/02 raw compiler outputs retained, unselected, zero credit; fresh03 singleton proof-only repair leaves eight contracts unchanged. Full serializer reversed lexical comparison derives Lt/Eq/Gt mathematical meaning; canonical raw domain additionally derives Eq iff internal words equal. Rust iterator comparison/u8/Scalar invariant/Ord trait/collection/primitive/compiler/full trace/cache/snapshot/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('corrected source-ordered finalizer composed into absent-start returned whole block publication','symbolic reversed typed serializer byte ordering derives exact mathematical scalar comparison')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':928,'owned_modules':104,'rejected_kernel':2})
