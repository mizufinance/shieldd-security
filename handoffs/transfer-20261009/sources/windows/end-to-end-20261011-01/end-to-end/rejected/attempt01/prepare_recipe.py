"""Prepare ordinary returned pipeline and actual rollback composition."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-writer-recover-current-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-host-seal-20261011-02'", "UPSTREAM = DIAG / 'transfer-writer-recover-current-20261011-02'")
replace("POOL = DIAG / 'transfer-writer-recover-current-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-end-to-end-owned-floor-20261011-01'")
replace("MODULE = 'TransferWriterRecoverCurrent01'", "MODULE = 'TransferEndToEnd01'")
replace("stdout = UPSTREAM / 'runs/01-TransferHostSeal01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWriterRecoverCurrent01/stdout.txt'")
replace("assert len(current) == 7", "assert len(current) == 13")
replace("records.append(('TransferHostSeal01'", "records.append(('TransferWriterRecoverCurrent01'")
replace("    'handwritten/TransferHostSeal01.lean', 'project/ShielddSecurity/TransferHostSeal01.lean']", "    'handwritten/TransferWriterRecoverCurrent01.lean', 'project/ShielddSecurity/TransferWriterRecoverCurrent01.lean']")
replace("assert len(records) == 67 and len(audits) == 670", "assert len(records) == 68 and len(audits) == 683")
replace("'objects': 67", "'objects': 68")
s=s.replace('sixty-seven-module','sixty-eight-module').replace('670 inherited','683 inherited')
start=s.index('\nmapping = ');end=s.index('\nmapping_file',start)
scope='Composed ordinary source Host end_block, seal_commit and commit threads each exact returned Host/Store into the next actual call. Returned root derives original InBlock/actual height, actual transfer state and pending ordered vector, same Frozen and boundary throughout prepare/seal/commit, actual seal lock/intent, actual completed participants and capacity, final Idle/cleared block/Ready owner/exact physical recovered Store with root/16-partition/history checks and independently observed current health. Conditional equivalence to captured-initial native recovery states ForwardPartitionFrames explicitly. Host rollback executes actual recover_current then independently observed App reconstruction; failures retain actual writer/Store progress with old Host phase/application/block id, clean reconstruction alone reaches Idle/deferred mode/new actual application. Thirteen complete reports (eight data/program definitions, five proofs). Ordinary returned pipeline is not initialized genesis/checkpoint or whole runtime certification. Component pending field correspondence, finite codec/root/version/height/hash/serde, snapshot raw/proof coherence plus separate ICS23 soundness, Arc/locks/registry/Clone/owner/concurrency/library/OS durability and genuine native replay remain explicit interfaces. Zero native/control/full certification.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"],\n    'scope': "+repr(scope)+"}"+s[end:]
replace("'imports': ['ShielddSecurity.TransferHostSeal01']", "'imports': ['ShielddSecurity.TransferWriterRecoverCurrent01']")
start=s.index("plan['kind'] = ");end=s.index("plan['artifact_policy']",start)
s=s[:start]+"plan['kind'] = 'SOURCE_COMPOSED_ORDINARY_TRANSFER_PIPELINE_AND_ACTUAL_HOST_ROLLBACK'\nplan['scope'] = mapping['scope']\nplan['source_repairs'] = 'Fresh source composition; original failed attempts retained with zero credit. No guard changes.'\n"+s[end:]
replace('WRITER_CURRENT_RECOVERY_COMPLETE_SIXTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','COMPOSED_TRANSFER_PIPELINE_COMPLETE_SIXTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
replace("'fresh_audits': 13, 'inherited_audits': 670", "'fresh_audits': 13, 'inherited_audits': 683")
(ROOT/'prepare.py').write_text(s)
print({'fresh_definitions_and_proofs':13,'reused_modules':68,'reused_full_reports':683,'scope':scope})
