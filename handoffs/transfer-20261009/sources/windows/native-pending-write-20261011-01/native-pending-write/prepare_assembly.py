"""Seal complete primitive-write audits on the preserved source closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-seal-transfer-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-seal-transfer-20261011-03'", "CURRENT = DIAG / 'transfer-native-pending-write-20261011-01'")
s=s.replace('transfer-native-seal-transfer-checkpoint-20261011-03','transfer-native-pending-write-checkpoint-20261011-01').replace('native-seal-transfer-endpoint','native-pending-write-endpoint')
replace("MODULE = 'TransferNativeSealTransfer01'", "MODULE = 'TransferNativePendingWrite01'")
replace("assert pool['objects'] == 71 and len(pool['inherited_public_reports']) == 715", "assert pool['objects'] == 72 and len(pool['inherited_public_reports']) == 718")
replace("manager_endpoint = DIAG / 'transfer-bounded-native-codec-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-native-seal-transfer-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-bounded-native-codec-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-seal-transfer-endpoint01.tar.xz'")
replace('59a11adc6ac2c0a19c8bcfdd34ed06dafc00ab8fb5ae464e9f548819dabff1fd','7257f945b81834122a4250780738409aa50c60c34623218e789780be6e715451')
replace("tar.extractfile('reports/fresh-14-complete-declarations.txt')", "tar.extractfile('reports/fresh-3-complete-declarations.txt')")
replace('assert len(manager_reports) == 14','assert len(manager_reports) == 3')
replace("'module': 'TransferBoundedNativeCodec01'", "'module': 'TransferNativeSealTransfer01'")
replace('assert len(combined_reports) == 715','assert len(combined_reports) == 718')
replace('assert len(manager_selected) == 71','assert len(manager_selected) == 72')
replace("reference = {'bounded_native_codec':", "reference = {'native_seal_transfer':")
replace("'imported_complete_reports': 14", "'imported_complete_reports': 3")
replace("'complete_owned_modules': 71, 'inherited_complete_reports': 715", "'complete_owned_modules': 72, 'inherited_complete_reports': 718")
s=s.replace('seventy-one-module','seventy-two-module').replace('715 original inherited','718 original inherited').replace('verified 715 inherited','verified 718 inherited')
replace("'inherited_complete_public_audits': 715", "'inherited_complete_public_audits': 718")
replace("'fresh_audits': 3, 'inherited_audits': 715", "'fresh_audits': 3, 'inherited_audits': 718",2)
replace('SOURCE_REACHED_NATIVE_SEAL_TRANSFER_EXACT_GLOBAL_INPUT_PUBLICATION_QUALIFIED','SOURCE_SUPPORTED_CANONICAL_NATIVE_PENDING_PRIMITIVE_WRITES_QUALIFIED')
replace("'rejected_attempts': 1", "'rejected_attempts': 0")
start=s.index("for suffix, role in [('01'");end=s.index("add(stdout, 'reports/fresh-3-complete-declarations.txt'",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Three original complete full types/axioms retained. New primitive write coverage does not require successful whole-body/commit/final-state storage. Restricted native encoder contract is only coherent canonical consensus-capacity values. All historical originals remain pinned and carried by ancestry, zero replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':3,'inherited_reports':718,'owned_modules':72,'rejected_attempts':0})
