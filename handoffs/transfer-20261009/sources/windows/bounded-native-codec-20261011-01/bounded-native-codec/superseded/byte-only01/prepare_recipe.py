"""Restrict native typed obligation to reachable finite nullifier values."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-global-commit-join-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-end-to-end-20261011-02'", "UPSTREAM = DIAG / 'transfer-global-commit-join-20261011-01'")
replace("POOL = DIAG / 'transfer-global-commit-join-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-bounded-native-codec-owned-floor-20261011-01'")
replace("MODULE = 'TransferGlobalCommitJoin01'", "MODULE = 'TransferBoundedNativeCodec01'")
replace("stdout = UPSTREAM / 'runs/01-TransferEndToEnd01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferGlobalCommitJoin01/stdout.txt'")
replace('assert len(current) == 13','assert len(current) == 5')
replace("records.append(('TransferEndToEnd01'", "records.append(('TransferGlobalCommitJoin01'")
replace("    'handwritten/TransferEndToEnd01.lean', 'project/ShielddSecurity/TransferEndToEnd01.lean']", "    'handwritten/TransferGlobalCommitJoin01.lean', 'project/ShielddSecurity/TransferGlobalCommitJoin01.lean']")
replace('assert len(records) == 69 and len(audits) == 696','assert len(records) == 70 and len(audits) == 701')
replace("'objects': 69", "'objects': 70")
s=s.replace('sixty-nine-module','seventy-module').replace('696 inherited','701 inherited')
replace('assert len(names) == 5','assert len(names) == 13')
start=s.index('\nmapping = ');end=s.index('\nmapping_file',start)
scope='NativePending codec obligation restricted to supported finite enum values: ordered/member vectors at most source consensus cap32768 and every projected nullifier key below2^256. Separate sum ghost branch totalizes unsupported abstract Nat values for reuse of accepted source-model theorem closure; no unsupported value claimed to be an actual Rust object. Successful bounded whole step derives supported next pending before rewriting its stored encoding to native inl. Symbolic arbitrary successful walk from encoded default derives every intermediate and final pending remains bounded and native branch. Composed default whole walk through actual end_block/seal/commit obtains exact global inputs, all input keys finite, Nodup/capacity and final observed physical root/boundary/ready/current health under only supported native codec roundtrip plus explicit native action-input byte projection and finalization field contract. Thirteen complete reports (five definitions, eight proofs). Other-object embedding/typed getter/Clone/finite collections, actual native trace projection, component field/panic, native temporal partition/poison/root/owner/locks, snapshot raw/proof coherence/separate ICS23/library/hash/serde/OS durability and genuine replay remain interfaces. No native enum branch proof beyond successful model writes, and zero native/control/full certification.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"],\n    'scope': "+repr(scope)+"}"+s[end:]
replace("'imports': ['ShielddSecurity.TransferEndToEnd01']", "'imports': ['ShielddSecurity.TransferGlobalCommitJoin01']")
start=s.index("plan['kind'] = ");end=s.index("plan['artifact_policy']",start)
s=s[:start]+"plan['kind'] = 'SOURCE_REACHABLE_FINITE_NATIVE_CODEC_AND_BOUNDED_WHOLE_PUBLICATION_CAPSTONE'\nplan['scope'] = mapping['scope']\nplan['source_repairs'] = 'Fresh reachable native-domain restriction and source capstone reuse; prior whole rejected attempts retained with zero credit. Guards unchanged.'\n"+s[end:]
replace('GLOBAL_COMMIT_JOIN_COMPLETE_SIXTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','BOUNDED_NATIVE_CODEC_COMPLETE_SEVENTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
replace("'fresh_audits': 5, 'inherited_audits': 696", "'fresh_audits': 13, 'inherited_audits': 701")
(ROOT/'prepare.py').write_text(s)
print({'fresh_definitions_and_proofs':13,'reused_modules':70,'reused_full_reports':701,'scope':scope})
