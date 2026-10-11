"""Seal symbolic scalar range with exact complete ancestry and failed repair evidence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-only-publication-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-only-publication-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-serialization-range-20261011-02'")
s=s.replace('transfer-native-only-publication-checkpoint-20261011-01','transfer-scalar-serialization-range-checkpoint-20261011-02').replace('native-only-publication-endpoint','scalar-serialization-range-endpoint')
replace("MODULE = 'TransferNativeOnlyPublication01'", "MODULE = 'TransferScalarSerializationRange01'")
replace('assert len(fresh) == 1','assert len(fresh) == 8')
replace("assert pool['objects'] == 77 and len(pool['inherited_public_reports']) == 737", "assert pool['objects'] == 78 and len(pool['inherited_public_reports']) == 738")
replace("manager_endpoint = DIAG / 'transfer-native-reachable-erasure-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-native-only-publication-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-reachable-erasure-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-only-publication-endpoint01.tar.xz'")
replace('0094261db42f951ac771c0e5a5ab49551794cf2482bf12a225edef3a7e217646','7c701a3ada374c7c3b585c1837c3137345de471517b126460767d4d31e650496')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-1-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 1')
replace("'module': 'TransferNativeReachableErasure01'", "'module': 'TransferNativeOnlyPublication01'")
replace('assert len(combined_reports) == 737','assert len(combined_reports) == 738')
replace('assert len(manager_selected) == 77','assert len(manager_selected) == 78')
replace("reference = {'native_reachable_erasure':", "reference = {'native_only_publication':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 1")
replace("'complete_owned_modules': 77, 'inherited_complete_reports': 737", "'complete_owned_modules': 78, 'inherited_complete_reports': 738")
s=s.replace('seventy-seven-module','seventy-eight-module').replace('737 original inherited','738 original inherited').replace('verified 737 inherited','verified 738 inherited')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 3")
replace("'fresh_theorem_audits': 1", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 1", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 737", "'inherited_complete_public_audits': 738")
replace("'fresh_audits': 1, 'inherited_audits': 737", "'fresh_audits': 8, 'inherited_audits': 738",2)
replace('SOURCE_NATIVE_ONLY_DEFAULT_WALK_WHOLE_PUBLICATION_SINGLE_ACTUAL_SEALED_GETTER_QUALIFIED','SOURCE_SCALAR_SERIALIZATION_SYMBOLIC_RANGE_FOUR_U64_ROUNDS_QUALIFIED')
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
replace("add(stdout, 'reports/fresh-1-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
anchor="add(stdout, 'reports/fresh-8-complete-declarations.txt'"
extra='''
add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact proof-only repair derivation source')
failed=DIAG/'transfer-scalar-serialization-range-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarSerializationRange01.lean','project/ShielddSecurity/TransferScalarSerializationRange01.lean','runs/01-TransferScalarSerializationRange01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected/01/'+n,'failed original rewrite/lint diagnostic; zero proof/control credit')
'''
s=s.replace(anchor,extra+'\n'+anchor,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All eight complete full type/axiom reports retained. One original failed algebraic rewrite and unused simp argument diagnostic retained with zero credit; fresh02 proof-only repair changes no declaration statements or guards. Scalar source/runtime/domain identities reused; machine-word/carry/byte correspondence remains explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':738,'owned_modules':78,'rejected_attempts':1})
