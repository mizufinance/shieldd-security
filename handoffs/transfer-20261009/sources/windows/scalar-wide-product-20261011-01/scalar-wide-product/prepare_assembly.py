"""Seal first-pass symbolic source-shaped full schoolbook product."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-choice-bit-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-choice-bit-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-wide-product-20261011-01'")
s=s.replace('transfer-scalar-choice-bit-checkpoint-20261011-01','transfer-scalar-wide-product-checkpoint-20261011-01').replace('scalar-choice-bit-endpoint','scalar-wide-product-endpoint')
replace("MODULE = 'TransferScalarChoiceBit01'", "MODULE = 'TransferScalarWideProduct01'")
replace('assert len(fresh) == 8','assert len(fresh) == 7')
replace("assert pool['objects'] == 108 and len(pool['inherited_public_reports']) == 954", "assert pool['objects'] == 109 and len(pool['inherited_public_reports']) == 962")
replace("manager_endpoint = DIAG / 'transfer-scalar-byte-decode-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-choice-bit-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-byte-decode-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-choice-bit-endpoint01.tar.xz'")
replace('b559acfc4141278172497565af436eca1f750900565fc4ce5db91285ed6e217c','e6acc6e507544b9eb0182ede867c1f183093ec8ade997bfe530a1b466c3f807a')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-8-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 8')
replace("'module': 'TransferScalarByteDecode01'", "'module': 'TransferScalarChoiceBit01'")
replace('assert len(combined_reports) == 954','assert len(combined_reports) == 962')
replace('assert len(manager_selected) == 108','assert len(manager_selected) == 109')
replace("reference = {'scalar_byte_decode':", "reference = {'scalar_choice_bit':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 8")
replace("'complete_owned_modules': 108, 'inherited_complete_reports': 954", "'complete_owned_modules': 109, 'inherited_complete_reports': 962")
s=s.replace('one-hundred-eight-module','one-hundred-nine-module').replace('954 original inherited','962 original inherited').replace('verified 954 inherited','verified 962 inherited')
replace("'fresh_theorem_audits': 6", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 8", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 954", "'inherited_complete_public_audits': 962")
replace("'fresh_audits': 8, 'inherited_audits': 954", "'fresh_audits': 7, 'inherited_audits': 962",2)
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
s=s.replace('SOURCE_FINITE_BORROW_MASK_LOW_CHOICE_BIT_QUALIFIED','SOURCE_SYMBOLIC_SCHOOLBOOK_FULL_WIDE_PRODUCT_QUALIFIED')
needle="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
replace(needle,needle+"\nrow = mapping['wide_product_source_shape']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/wide-product-shape.json', 'exact16 MAC retained-row/carry static source association; primitive/compiler/final wide reduction binding separate')")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. First kernel attempt passed. Actual modeled16 MAC symbolic row schedule derives exact eight-limb width/full integer product/range; desired product is a conclusion, not supplied state. Exact pinned source16call shape is static association. Native primitive/compiler/full trace and final wide Montgomery reduction bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('exact source-shaped low choice bit derives canonical acceptance and noncanonical refusal','symbolic source-shaped full16 MAC product, width and full integer value')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':962,'owned_modules':109,'first_attempt_passed':True})
