"""Seal bounded exact-Item body and delivery/index model equality."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-native-ghost-erasure-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-native-ghost-erasure-20261011-02'", "CURRENT = DIAG / 'transfer-native-delivery-erasure-20261011-01'")
s=s.replace('transfer-native-ghost-erasure-checkpoint-20261011-02','transfer-native-delivery-erasure-checkpoint-20261011-01').replace('native-ghost-erasure-endpoint','native-delivery-erasure-endpoint')
replace("MODULE = 'TransferNativeGhostErasure01'", "MODULE = 'TransferNativeDeliveryErasure01'")
replace('assert len(fresh) == 5','assert len(fresh) == 4')
replace("assert pool['objects'] == 74 and len(pool['inherited_public_reports']) == 724", "assert pool['objects'] == 75 and len(pool['inherited_public_reports']) == 729")
replace("manager_endpoint = DIAG / 'transfer-native-raw-pending-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-native-ghost-erasure-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-native-raw-pending-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-native-ghost-erasure-endpoint01.tar.xz'")
replace('fc91e3068055cfbf8e10b857ecc00048c9ad0e617a59e627aa354c88856a8dbb','cb1fc96e7dc67da608aa70a37f3b9a0ed466782cf4ebaec4bf49142616be90b0')
replace("tar.extractfile('reports/fresh-3-complete-declarations.txt')", "tar.extractfile('reports/fresh-5-complete-declarations.txt')")
replace('assert len(manager_reports) == 3','assert len(manager_reports) == 5')
replace("'module': 'TransferNativeRawPending01'", "'module': 'TransferNativeGhostErasure01'")
replace('assert len(combined_reports) == 724','assert len(combined_reports) == 729')
replace('assert len(manager_selected) == 74','assert len(manager_selected) == 75')
replace("reference = {'native_raw_pending':", "reference = {'native_ghost_erasure':")
replace("'imported_complete_reports': 3", "'imported_complete_reports': 5")
replace("'complete_owned_modules': 74, 'inherited_complete_reports': 724", "'complete_owned_modules': 75, 'inherited_complete_reports': 729")
s=s.replace('seventy-four-module','seventy-five-module').replace('724 original inherited','729 original inherited').replace('verified 724 inherited','verified 729 inherited')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 0")
replace("'fresh_complete_public_audits': 5", "'fresh_complete_public_audits': 4")
replace("'inherited_complete_public_audits': 724", "'inherited_complete_public_audits': 729")
replace("'fresh_audits': 5, 'inherited_audits': 724", "'fresh_audits': 4, 'inherited_audits': 729",2)
replace('SOURCE_BOUNDED_CANONICAL_PENDING_GHOST_ERASURE_ALL_RETURN_PRIMITIVE_RAW_QUALIFIED','SOURCE_BOUNDED_CANONICAL_PENDING_CAPABILITY_BODY_AND_EXACT_DELIVERY_ERASURE_QUALIFIED')
replace("'rejected_attempts': 1", "'rejected_attempts': 0")
start=s.index("failed=DIAG/'transfer-native-ghost-erasure-20261011-01'");end=s.index("add(stdout, 'reports/fresh-5-complete-declarations.txt'",start)
s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'", "add(stdout, 'reports/fresh-4-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four original complete full types/axioms retained. Exact complete-Item re-extraction/body equality covers every returned result; actual initial-child body equality determines exact delivery parent/events/queue or refusal in every index mode using identical observations. Same extended state type remains on both sides; no native Rust trace/codec/getter closure. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':729,'owned_modules':75,'rejected_attempts':0})
