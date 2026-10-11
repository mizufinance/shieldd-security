"""Seal exact native-shaped borrow mask cast and canonical choice byte."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-byte-decode-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-byte-decode-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-choice-bit-20261011-01'")
s=s.replace('transfer-scalar-byte-decode-checkpoint-20261011-02','transfer-scalar-choice-bit-checkpoint-20261011-01').replace('scalar-byte-decode-endpoint','scalar-choice-bit-endpoint')
replace("MODULE = 'TransferScalarByteDecode01'", "MODULE = 'TransferScalarChoiceBit01'")
replace('assert len(fresh) == 7','assert len(fresh) == 8')
replace("assert pool['objects'] == 107 and len(pool['inherited_public_reports']) == 947", "assert pool['objects'] == 108 and len(pool['inherited_public_reports']) == 954")
replace("manager_endpoint = DIAG / 'transfer-partition-local-rollback-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-scalar-byte-decode-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-partition-local-rollback-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-byte-decode-endpoint01.tar.xz'")
replace('2da4cb39c290435e018021dd77e20cdc073e9c6af1bfa429e3737ad02c0389c8','b559acfc4141278172497565af436eca1f750900565fc4ce5db91285ed6e217c')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 7')
replace("'module': 'TransferPartitionLocalRollback01'", "'module': 'TransferScalarByteDecode01'")
replace('assert len(combined_reports) == 947','assert len(combined_reports) == 954')
replace('assert len(manager_selected) == 107','assert len(manager_selected) == 108')
replace("reference = {'partition_local_rollback':", "reference = {'scalar_byte_decode':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 107, 'inherited_complete_reports': 947", "'complete_owned_modules': 108, 'inherited_complete_reports': 954")
s=s.replace('one-hundred-seven-module','one-hundred-eight-module').replace('947 original inherited','954 original inherited').replace('verified 947 inherited','verified 954 inherited')
replace("'fresh_theorem_audits': 5", "'fresh_theorem_audits': 6")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 947", "'inherited_complete_public_audits': 954")
replace("'fresh_audits': 7, 'inherited_audits': 947", "'fresh_audits': 8, 'inherited_audits': 954",2)
s=s.replace('SOURCE_TYPED_BYTE_DECODE_CANONICAL_BORROW_QUALIFIED','SOURCE_FINITE_BORROW_MASK_LOW_CHOICE_BIT_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-7-complete-declarations.txt'",start);s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. First kernel attempt passed. Exact modeled u64 borrow mask cast to u8 and bitwise AND1 yields0/1; success/refusal bits derive parsed value below/at-or-above p; exact serializer bytes derive one. Native Choice/CtOption/R2 payload conversion/Scalar invariant/primitive/compiler/full trace binding remains explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('symbolic finite byte-word parser reconstructs exact integer and source-shaped canonical borrow accept predicate','exact source-shaped low choice bit derives canonical acceptance and noncanonical refusal')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':954,'owned_modules':108,'first_attempt_passed':True})
