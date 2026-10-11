"""Prepare fixed native codec and any-return raw reshape pending retention."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-native-pending-write-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-seal-transfer-20261011-03'", "UPSTREAM = DIAG / 'transfer-native-pending-write-20261011-01'")
replace("POOL = DIAG / 'transfer-native-pending-write-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-native-raw-pending-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativePendingWrite01'", "MODULE = 'TransferNativeRawPending01'")
s=s.replace("'runs/01-TransferNativeSealTransfer01/stdout.txt'", "'runs/01-TransferNativePendingWrite01/stdout.txt'",1)
replace("records.append(('TransferNativeSealTransfer01'", "records.append(('TransferNativePendingWrite01'")
replace("    'handwritten/TransferNativeSealTransfer01.lean', 'project/ShielddSecurity/TransferNativeSealTransfer01.lean']]", "    'handwritten/TransferNativePendingWrite01.lean', 'project/ShielddSecurity/TransferNativePendingWrite01.lean']]")
replace('assert len(records) == 72 and len(audits) == 718', 'assert len(records) == 73 and len(audits) == 721')
replace("'objects': 72", "'objects': 73")
s=s.replace('seventy-two-module','seventy-three-module').replace('718 inherited','721 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeSealTransfer01']", "'imports': ['ShielddSecurity.TransferNativePendingWrite01']")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Fixed accepted finite native codec installs the source primitive encoder. Primitive native write conclusion is derived without separate encoder correspondence hypothesis, using canonical supported codec branch. Actual successful primitive inside source raw reshape yields coherent Nodup Open consensus-capacity/canonical-domain next pending. Exact admitted native pending object retained by every returned subsequent note/SCT reshape outcome, including errors, using original all-outcome distinct-key frames. No whole raw/body/commit success premise. One definition and two complete proofs. Unsupported ghost values remain proof-only, actual native codec/getter/field-byte/Clone/finite library/input projection/trace/key identity, authenticated reader/crypto/snapshot/ownership/temporal/locks/OS remain interfaces. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh fixed-codec native primitive and any-return raw-reshape frame join; removes extra source-model encoder premise and no whole-body-success assumption. Qualified primitive3 reused on complete 721-report/73-module ancestry without replay. Historical originals retained; physical and per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_CANONICAL_NATIVE_PENDING_PRIMITIVE_ALL_BRANCH_WRITES','SOURCE_FIXED_CODEC_CANONICAL_NATIVE_PENDING_ANY_RETURN_RAW_RESHAPE')
s=s.replace('NATIVE_PRIMITIVE_WRITE_COMPLETE_SEVENTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_RAW_PENDING_COMPLETE_SEVENTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 718", "'inherited_audits': 721")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'inherited_reports':721,'owned_modules':73})
