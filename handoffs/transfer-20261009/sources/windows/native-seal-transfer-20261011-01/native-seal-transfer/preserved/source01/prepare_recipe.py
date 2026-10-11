"""Cover canonical native pending through source SCT seal and actual transfer."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-bounded-native-codec-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-global-commit-join-20261011-01'", "UPSTREAM = DIAG / 'transfer-bounded-native-codec-20261011-02'")
replace("POOL = DIAG / 'transfer-bounded-native-codec-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-native-seal-transfer-owned-floor-20261011-01'")
replace("MODULE = 'TransferBoundedNativeCodec01'", "MODULE = 'TransferNativeSealTransfer01'")
replace("stdout = UPSTREAM / 'runs/01-TransferGlobalCommitJoin01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferBoundedNativeCodec01/stdout.txt'")
replace('assert len(current) == 5','assert len(current) == 14')
replace("records.append(('TransferGlobalCommitJoin01'", "records.append(('TransferBoundedNativeCodec01'")
replace("    'handwritten/TransferGlobalCommitJoin01.lean', 'project/ShielddSecurity/TransferGlobalCommitJoin01.lean']", "    'handwritten/TransferBoundedNativeCodec01.lean', 'project/ShielddSecurity/TransferBoundedNativeCodec01.lean']")
replace('assert len(records) == 70 and len(audits) == 701','assert len(records) == 71 and len(audits) == 715')
replace("'objects': 70", "'objects': 71")
s=s.replace('seventy-module','seventy-one-module').replace('701 inherited','715 inherited')
replace('assert len(names) == 14','assert len(names) == 3')
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Canonical shared-field bounded Pending source SCT seal stores supported native Sealed enum of its actual current ordered input. Actual finalization field contract and derived concrete state-transfer object frame preserve that same native sealed object in exact returned state. Whole bounded default walk through ordinary end_block/seal/commit derives actual transferred object some native Sealed exact allInputs requests, Nodup/cap32768/all canonical Fq identities, same writer accepted inputs/application root/Ready/Idle/final observed nullifier roots and stored boundary. Three complete proofs; every modeled reachable staging and SCT seal pending write covered by inherited bounded domain plus new source seal/transfer derivation. Native canonical-field byte projection, typed enum embedding/Clone/Any/Arc/other-object/finite library, actual component returned field and panic/trace/ownership/locks/snapshot coherence/separate ICS23/physical partition/hash/serde/OS/genuine replay remain interfaces. Ghost unsupported branch never asserted as native or used by reachable pending source writes. Zero native/control/full certification.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"],\n    'scope': "+repr(scope)+"}"+s[end:]
replace("'imports': ['ShielddSecurity.TransferGlobalCommitJoin01']", "'imports': ['ShielddSecurity.TransferBoundedNativeCodec01']")
replace("domain = json.loads((ROOT/'context/canonical-domain.json').read_bytes())", "domain = json.loads((DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json').read_bytes())")
replace("pin(ROOT/'context/canonical-domain.json')", "pin(DIAG/'transfer-bounded-native-codec-20261011-02/context/canonical-domain.json')")
replace("pin(ROOT/'prepare_recipe_count_failure.py')", "pin(DIAG/'transfer-bounded-native-codec-20261011-02/prepare_recipe_count_failure.py')")
replace("'crates/core/app/src/app/host.rs', 'crates/core/app/src/app/lifecycle.rs'", "'crates/core/component/sct/src/component/sct.rs', 'crates/core/app/src/app/host.rs', 'crates/core/app/src/app/lifecycle.rs'")
start=s.index("plan['kind'] = ");end=s.index("plan['artifact_policy']",start)
s=s[:start]+"plan['kind'] = 'SOURCE_CANONICAL_NATIVE_PENDING_SCT_SEAL_ACTUAL_TRANSFER_AND_WHOLE_PUBLICATION'\nplan['scope'] = mapping['scope']\nplan['source_repairs'] = 'Fresh native reachable seal/transfer source join on qualified canonical bounded codec. No ancestor/field replay; all prior receipts retained, guards unchanged.'\n"+s[end:]
replace('BOUNDED_NATIVE_CODEC_COMPLETE_SEVENTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_SEAL_TRANSFER_COMPLETE_SEVENTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
replace("'fresh_audits': 14, 'inherited_audits': 701", "'fresh_audits': 3, 'inherited_audits': 715")
(ROOT/'prepare.py').write_text(s)
print({'fresh_definitions_and_proofs':3,'reused_modules':71,'reused_full_reports':715,'scope':scope})
