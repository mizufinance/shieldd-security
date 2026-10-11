"""Prepare supported native primitive writes independent of later body success."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-native-seal-transfer-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-bounded-native-codec-20261011-02'", "UPSTREAM = DIAG / 'transfer-native-seal-transfer-20261011-03'")
replace("POOL = DIAG / 'transfer-native-seal-transfer-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-native-pending-write-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativeSealTransfer01'", "MODULE = 'TransferNativePendingWrite01'")
s=s.replace("'runs/01-TransferBoundedNativeCodec01/stdout.txt'", "'runs/01-TransferNativeSealTransfer01/stdout.txt'",1)
replace('assert len(current) == 14','assert len(current) == 3')
replace("records.append(('TransferBoundedNativeCodec01'", "records.append(('TransferNativeSealTransfer01'")
replace("    'handwritten/TransferBoundedNativeCodec01.lean', 'project/ShielddSecurity/TransferBoundedNativeCodec01.lean']]", "    'handwritten/TransferNativeSealTransfer01.lean', 'project/ShielddSecurity/TransferNativeSealTransfer01.lean']]")
replace('assert len(records) == 71 and len(audits) == 715', 'assert len(records) == 72 and len(audits) == 718')
replace("'objects': 71", "'objects': 72")
s=s.replace('seventy-one-module','seventy-two-module').replace('715 inherited','718 inherited')
replace("'imports': ['ShielddSecurity.TransferBoundedNativeCodec01']", "'imports': ['ShielddSecurity.TransferNativeSealTransfer01']")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Modeled pending nullifier primitive inspection derives coherent Nodup Open ordered append, consensus capacity and canonical shared-field bounds, hence supported finite native enum. Restricted encoder correspondence only for coherent capacity-bounded canonical pending values. Any actual successful nonempty primitive writes the exact native enum object visible in child state. Every modeled executeNullify branch retains original input cache or writes that supported native object, independently of subsequent raw note/SCT/body success and without whole commit/final-state success. Three complete proofs; no universal ghost encoding contract and no blanket native heap/trace correspondence. Native getter/field-byte projection/typed objects/Clone/finite collections, authenticated reader/merkle/crypto/current health/temporal/snapshot/locks/Arc/ownership/OS remain explicit interfaces. Zero native, control and certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh primitive write coverage independent of later raw-body/commit success, using original actual inspection and single-write source model. Reached native-seal source03 passed3 reused with entire qualified 718-report/72-module closure, no replay. All historical originals retained; physical and per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_CANONICAL_NATIVE_PENDING_SCT_SEAL_ACTUAL_TRANSFER_AND_WHOLE_PUBLICATION','SOURCE_CANONICAL_NATIVE_PENDING_PRIMITIVE_ALL_BRANCH_WRITES')
s=s.replace('NATIVE_SEAL_TRANSFER_COMPLETE_SEVENTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_PRIMITIVE_WRITE_COMPLETE_SEVENTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 715", "'inherited_audits': 718")
(ROOT/'prepare.py').write_text(s)
print({'fresh_proofs':3,'inherited_reports':718,'owned_modules':72})
