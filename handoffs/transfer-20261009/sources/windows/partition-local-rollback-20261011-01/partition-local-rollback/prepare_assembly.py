"""Seal partition-local root frame and captured recovery reuse."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-byte-key-cache-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-byte-key-cache-20261011-04'", "CURRENT = DIAG / 'transfer-partition-local-rollback-20261011-01'")
s=s.replace('transfer-byte-key-cache-checkpoint-20261011-04','transfer-partition-local-rollback-checkpoint-20261011-01').replace('byte-key-cache-endpoint','partition-local-rollback-endpoint')
replace("MODULE = 'TransferByteKeyCache01'", "MODULE = 'TransferPartitionLocalRollback01'")
replace('assert len(fresh) == 7','assert len(fresh) == 4')
replace("assert pool['objects'] == 105 and len(pool['inherited_public_reports']) == 936", "assert pool['objects'] == 106 and len(pool['inherited_public_reports']) == 943")
replace("manager_endpoint = DIAG / 'transfer-scalar-reversed-byte-order-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-byte-key-cache-endpoint-20261011-04'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-reversed-byte-order-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-byte-key-cache-endpoint01.tar.xz'")
replace('954d498478cb9749362d35adc6e0521982f6a5571e99b042340950a67f4d8736','82ee220d7abecd91552a653ea8e9a4b2e0e690b6230ea9088452225e96afbef7')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 7')
replace("'module': 'TransferScalarReversedByteOrder01'", "'module': 'TransferByteKeyCache01'")
replace('assert len(combined_reports) == 936','assert len(combined_reports) == 943')
replace('assert len(manager_selected) == 105','assert len(manager_selected) == 106')
replace("reference = {'scalar_reversed_byte_order':", "reference = {'byte_key_cache':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 105, 'inherited_complete_reports': 936", "'complete_owned_modules': 106, 'inherited_complete_reports': 943")
s=s.replace('one-hundred-five-module','one-hundred-six-module').replace('936 original inherited','943 original inherited').replace('verified 936 inherited','verified 943 inherited')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 1")
replace("'fresh_theorem_audits': 4", "'fresh_theorem_audits': 3")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 4")
replace("'inherited_complete_public_audits': 936", "'inherited_complete_public_audits': 943")
replace("'fresh_audits': 7, 'inherited_audits': 936", "'fresh_audits': 4, 'inherited_audits': 943",2)
replace("'rejected_attempts': 2", "'rejected_attempts': 0")
s=s.replace('SOURCE_EXACT_BYTE_KEY_CACHE_RELATION_QUALIFIED','SOURCE_PARTITION_LOCAL_ROLLBACK_FRAME_RECOVERY_REUSE_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-7-complete-declarations.txt'",start);s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-4-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete full type/axiom reports retained. First attempt passed. Partition-local model primitive provides independent own root and possible error; all other roots frame even on error. This derives ForwardPartitionFrames and exact captured/original recovery reuse; it assumes neither success nor own-root restoration or final health. No actual NOMT handle isolation/concurrent root/lock/library/native trace/filesystem/crash binding is claimed. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('exact byte-key observation relation preserves modeled cache update/delete/overlay/merge semantics','partition-local root update derives forward frame and complete captured/original recovery equivalence')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':943,'owned_modules':106,'first_attempt_passed':True})
