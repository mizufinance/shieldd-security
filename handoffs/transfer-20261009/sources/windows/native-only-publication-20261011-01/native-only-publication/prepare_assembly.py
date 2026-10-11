"""Seal native-only walk publication and single reached sealed getter contract."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-reachable-erasure-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-reachable-erasure-20261011-03'", "CURRENT = DIAG / 'transfer-native-only-publication-20261011-01'")
s=s.replace('transfer-native-reachable-erasure-checkpoint-20261011-03','transfer-native-only-publication-checkpoint-20261011-01').replace('native-reachable-erasure-endpoint','native-only-publication-endpoint')
replace("MODULE = 'TransferNativeReachableErasure01'", "MODULE = 'TransferNativeOnlyPublication01'")
replace('assert len(fresh) == 4','assert len(fresh) == 1')
replace("assert pool['objects'] == 76 and len(pool['inherited_public_reports']) == 733", "assert pool['objects'] == 77 and len(pool['inherited_public_reports']) == 737")
replace("manager_endpoint = DIAG / 'transfer-native-delivery-erasure-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-native-reachable-erasure-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-delivery-erasure-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-reachable-erasure-endpoint01.tar.xz'")
replace('a58c8d7905d47f6c52f257193883d6e54ab6ff788d600a448ddda8aa1b3331ae','0094261db42f951ac771c0e5a5ab49551794cf2482bf12a225edef3a7e217646')
replace("'module': 'TransferNativeDeliveryErasure01'", "'module': 'TransferNativeReachableErasure01'")
replace('assert len(combined_reports) == 733','assert len(combined_reports) == 737')
replace('assert len(manager_selected) == 76','assert len(manager_selected) == 77')
replace("reference = {'native_delivery_erasure':", "reference = {'native_reachable_erasure':")
replace("'complete_owned_modules': 76, 'inherited_complete_reports': 733", "'complete_owned_modules': 77, 'inherited_complete_reports': 737")
s=s.replace('seventy-six-module','seventy-seven-module').replace('733 original inherited','737 original inherited').replace('verified 733 inherited','verified 737 inherited')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 0")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 1")
replace("'fresh_complete_public_audits': 4", "'fresh_complete_public_audits': 1")
replace("'inherited_complete_public_audits': 733", "'inherited_complete_public_audits': 737")
replace("'fresh_audits': 4, 'inherited_audits': 733", "'fresh_audits': 1, 'inherited_audits': 737",2)
replace('SOURCE_BOUNDED_CANONICAL_PENDING_ACTUAL_REQUEST_AND_WHOLE_WALK_ERASURE_QUALIFIED','SOURCE_NATIVE_ONLY_DEFAULT_WALK_WHOLE_PUBLICATION_SINGLE_ACTUAL_SEALED_GETTER_QUALIFIED')
replace("'rejected_attempts': 2", "'rejected_attempts': 0")
start=s.index("for suffix in ['01','02']:");end=s.index("add(stdout, 'reports/fresh-4-complete-declarations.txt'",start)
s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-4-complete-declarations.txt'", "add(stdout, 'reports/fresh-1-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' One original complete full type/axiom report retained. Native default sum enum and native-only source walk supplied; equal accepted encoder walk derived. Exact global sealed inputs/accepted vector/application root/Ready/Idle/final roots and boundary follow source pipeline under reached finalization and ONE actual sealed enum getter equality. New signature intentionally narrows previous all-supported getter and changes walk/default premises; older originals immutable. Same extended object type/callbacks retained, zero native Rust codec/getter/input/trace closure. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':1,'inherited_reports':737,'owned_modules':77,'rejected_attempts':0})
