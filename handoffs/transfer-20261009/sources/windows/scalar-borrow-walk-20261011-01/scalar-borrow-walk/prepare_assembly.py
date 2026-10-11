"""Seal symbolic borrow walk with exact primitive and complete owned ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-sbb-primitive-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-sbb-primitive-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-borrow-walk-20261011-01'")
s=s.replace('transfer-scalar-sbb-primitive-checkpoint-20261011-02','transfer-scalar-borrow-walk-checkpoint-20261011-01').replace('scalar-sbb-primitive-endpoint','scalar-borrow-walk-endpoint')
replace("MODULE = 'TransferScalarSbbPrimitive01'", "MODULE = 'TransferScalarBorrowWalk01'")
replace('assert len(fresh) == 9','assert len(fresh) == 7')
replace("assert pool['objects'] == 83 and len(pool['inherited_public_reports']) == 785", "assert pool['objects'] == 84 and len(pool['inherited_public_reports']) == 794")
replace("manager_endpoint = DIAG / 'transfer-scalar-adc-shift-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-sbb-primitive-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-adc-shift-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-sbb-primitive-endpoint01.tar.xz'")
replace('f8109d3e4a3ac224848f165ef605064e60bd946d1f356d59fa813134a40faf2d','b318298fda5f99c975f545206dec9dfa99c943351f385acfed00ca2da470d541')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-9-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 9')
replace("'module': 'TransferScalarAdcShift01'", "'module': 'TransferScalarSbbPrimitive01'")
replace('assert len(combined_reports) == 785','assert len(combined_reports) == 794')
replace('assert len(manager_selected) == 83','assert len(manager_selected) == 84')
replace("reference = {'scalar_adc_shift':", "reference = {'scalar_sbb_primitive':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 9")
replace("'complete_owned_modules': 83, 'inherited_complete_reports': 785", "'complete_owned_modules': 84, 'inherited_complete_reports': 794")
s=s.replace('eighty-three-module','eighty-four-module').replace('785 original inherited','794 original inherited').replace('verified 785 inherited','verified 794 inherited')
replace("'fresh_definition_audits': 4", "'fresh_definition_audits': 2")
replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 785", "'inherited_complete_public_audits': 794")
replace("'fresh_audits': 9, 'inherited_audits': 785", "'fresh_audits': 7, 'inherited_audits': 794",2)
replace("'rejected_attempts': 1", "'rejected_attempts': 0")
replace('SOURCE_SCALAR_REACHABLE_BORROW_MASK_SBB_SINGLE_WORD_ARITHMETIC_QUALIFIED','SOURCE_SCALAR_SYMBOLIC_BORROW_WALK_AND_DERIVED_FINAL_UNDERFLOW_QUALIFIED')
replace("add(stdout, 'reports/fresh-9-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-7-complete-declarations.txt'",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained, first strict run passed. Next borrow Boolean agrees with actual source-shaped outgoing mask and full primitive equation; symbolic induction derives vector conservation and final underflow from finite output bound. Rust primitive/trace/conditional modulus add-back/endian correspondence remains an interface. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':794,'owned_modules':84,'rejected_attempts':0})
