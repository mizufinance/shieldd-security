"""Seal exact masked source normalization and immutable failed projection repair evidence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-borrow-walk-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-borrow-walk-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-masked-normalization-20261011-02'")
s=s.replace('transfer-scalar-borrow-walk-checkpoint-20261011-01','transfer-scalar-masked-normalization-checkpoint-20261011-02').replace('scalar-borrow-walk-endpoint','scalar-masked-normalization-endpoint')
replace("MODULE = 'TransferScalarBorrowWalk01'", "MODULE = 'TransferScalarMaskedNormalization01'")
replace('assert len(fresh) == 7','assert len(fresh) == 10')
replace("assert pool['objects'] == 84 and len(pool['inherited_public_reports']) == 794", "assert pool['objects'] == 85 and len(pool['inherited_public_reports']) == 801")
replace("manager_endpoint = DIAG / 'transfer-scalar-sbb-primitive-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-borrow-walk-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-sbb-primitive-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-borrow-walk-endpoint01.tar.xz'")
replace('b318298fda5f99c975f545206dec9dfa99c943351f385acfed00ca2da470d541','de678eaedd909ee01b9ff66f0abcd5e1cbad15ea9833ac839b8b40f288a51f3b')
replace("tar.extractfile('reports/fresh-9-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 9','assert len(manager_reports) == 7')
replace("'module': 'TransferScalarSbbPrimitive01'", "'module': 'TransferScalarBorrowWalk01'")
replace('assert len(combined_reports) == 794','assert len(combined_reports) == 801')
replace('assert len(manager_selected) == 84','assert len(manager_selected) == 85')
replace("reference = {'scalar_sbb_primitive':", "reference = {'scalar_borrow_walk':")
replace("'imported_complete_reports': 9", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 84, 'inherited_complete_reports': 794", "'complete_owned_modules': 85, 'inherited_complete_reports': 801")
s=s.replace('eighty-four-module','eighty-five-module').replace('794 original inherited','801 original inherited').replace('verified 794 inherited','verified 801 inherited')
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 8")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 10")
replace("'inherited_complete_public_audits': 794", "'inherited_complete_public_audits': 801")
replace("'fresh_audits': 7, 'inherited_audits': 794", "'fresh_audits': 10, 'inherited_audits': 801",2)
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
replace('SOURCE_SCALAR_SYMBOLIC_BORROW_WALK_AND_DERIVED_FINAL_UNDERFLOW_QUALIFIED','SOURCE_SCALAR_MASKED_SUBTRACTION_ADD_BACK_EXACT_NORMALIZATION_QUALIFIED')
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-10-complete-declarations.txt'")
anchor="add(stdout, 'reports/fresh-10-complete-declarations.txt'"
extra='''add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact proof-only actual projection repair derivation source')
failed=DIAG/'transfer-scalar-masked-normalization-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMaskedNormalization01.lean','project/ShielddSecurity/TransferScalarMaskedNormalization01.lean','runs/01-TransferScalarMaskedNormalization01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/01/'+n,'unfolded returned projection prevented case rewrite; all raw diagnostics, zero proof/control credit')
'''
s=s.replace(anchor,extra+anchor,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Ten complete full type/axiom reports retained. Failed01 unfolded return projection/case-rewrite mismatch retained with zero credit; fresh02 proof-only actual difference projection normalization leaves all ten contracts unchanged. Actual model final borrow/AND masks and truncated ADC sum derive exact source single-modulus normalization; composed four-round finite result lies in canonical field range. Rust trace/byte/endian/type/modular semantic correspondence remains an interface. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':10,'inherited_reports':801,'owned_modules':85,'rejected_attempts':1})
