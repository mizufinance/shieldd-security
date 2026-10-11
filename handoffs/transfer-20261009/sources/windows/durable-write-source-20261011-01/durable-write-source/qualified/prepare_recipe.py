"""Prepare file write/sync/drop/rename/directory-sync order and intent refusal join."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-authenticated-boundary-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-boundary-reader-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-writer-recovery-join-20261011-01'")
replace("POOL = DIAG / 'transfer-authenticated-boundary-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-durable-write-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferAuthenticatedBoundarySource01'", "MODULE = 'TransferDurableWriteSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferBoundaryReaderSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWriterRecoveryJoin01/stdout.txt'")
replace("records.append(('TransferBoundaryReaderSource01'", "records.append(('TransferWriterRecoveryJoin01'")
replace("'repair_recipe.py', 'handwritten/TransferBoundaryReaderSource01.lean', 'project/ShielddSecurity/TransferBoundaryReaderSource01.lean'", "'handwritten/TransferWriterRecoveryJoin01.lean', 'project/ShielddSecurity/TransferWriterRecoveryJoin01.lean'")
replace('assert len(current) == 7','assert len(current) == 6')
replace('assert len(records) == 55 and len(audits) == 551','assert len(records) == 58 and len(audits) == 576')
replace("'objects': 55", "'objects': 58")
s=s.replace('Complete fifty-five-module first owned root; 551 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-eight-module first owned root; 576 inherited full reports; shared StateDelta/Readback and original BankRecovery10 included exactly once.')
replace('assert len(names) == 9','assert len(names) == 8')
replace("'imports': ['ShielddSecurity.TransferBoundaryReaderSource01']", "'imports': ['ShielddSecurity.TransferWriterRecoveryJoin01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source durable_write parent/open-create-truncate-write temporary file/write_all/same observed handle sync/drop/rename/directory-sync sequence, with independently observed filesystem progress retained on every failure. Whole returned write success derives parent and all ordered fallible primitive returns and same file handle for write_all and file sync. Missing parent refuses before open with original modeled filesystem. Failed final directory sync after successful rename retains exactly the observed directory-sync output; it may contain the intent target and is never inferred absent. Actual source durable writer installed into source persist_intent derives interrupted modeled Store/status refusal and retained observed filesystem on returned write failure. Eight reports (four data/program definitions, four proofs), strict finite/physical guards unchanged. File drop is a nonfallible ghost observation of filesystem effects, not a native Result callback. Native exact path/extension/options/directory/file descriptor/ownership/OS/bytes/sync/rename/durability, Store-at-write ghost erasure and concurrent temporal/memory/physical-root correspondence remain explicit. No native/control/full Transfer certification or inferred rollback/absent target.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Io captures the selected native target/temporary/parent path context and open flags as explicit interfaces; observed Nat file handle represents the actual file used for write_all and sync_all, with native descriptor/type/ownership correspondence open. closeFile is a nonfallible ghost of observed filesystem effects of drop(file), not an added native Result-returning operation or concurrent trace proof. Callback filesystem progress is independent of succeeded and is retained at every failure; directory sync after rename may fail with target already present. Actual fs/file/OS durability and Store-at-write ghost/native memory/lock/physical root/async correspondence remain explicit; no root health or rollback/absence inferred from error.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_AUTHENTICATED_BOUNDARY_ROOT_KEY_PROOFS_READER_HEIGHT_AND_VALUE_COHERENCE','SOURCE_DURABLE_FILE_WRITE_ORDER_OBSERVED_PROGRESS_AND_INTENT_FAILURE')
s=s.replace('AUTHENTICATED_BOUNDARY_SOURCE_COMPLETE_FIFTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','DURABLE_WRITE_SOURCE_COMPLETE_FIFTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 9, 'inherited_audits': 551", "'fresh_audits': 8, 'inherited_audits': 576")
s=s.replace('complete fifty-five-module owned root','complete fifty-eight-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source durable-write returned call-order/same-handle/failure-progress proof and installed source intent refusal join; no imported replay or native filesystem/durability credit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_audits':576,'owned_modules':58})
