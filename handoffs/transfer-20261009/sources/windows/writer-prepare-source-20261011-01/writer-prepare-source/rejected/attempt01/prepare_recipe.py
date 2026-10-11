"""Prepare same source writer Ready-to-Prepared handoff with finite codec block inputs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-block-seal-join-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-pending-seal-source-20261011-03'", "UPSTREAM = DIAG / 'transfer-reachable-pending-block-20261011-03'")
replace("POOL = DIAG / 'transfer-block-seal-join-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-writer-prepare-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferBlockSealJoin01'", "MODULE = 'TransferWriterPrepareSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferPendingSealSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferReachablePendingBlock01/stdout.txt'")
replace("records.append(('TransferPendingSealSource01'", "records.append(('TransferReachablePendingBlock01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingSealSource01.lean', 'project/ShielddSecurity/TransferPendingSealSource01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generate.py', 'regeneration.json', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean']]")
replace('assert len(current) == 13','assert len(current) == 7')
replace('assert len(records) == 43 and len(audits) == 425','assert len(records) == 47 and len(audits) == 459')
replace("'objects': 43", "'objects': 47")
s=s.replace('Complete forty-three-module first owned root; 425 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-seven-module first owned root; 459 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 5','assert len(names) == 14')
replace("'imports': ['ShielddSecurity.TransferPendingSealSource01']", "'imports': ['ShielddSecurity.TransferReachablePendingBlock01']")
replace("for relative in ['crates/core/component/sct/src/component/sct.rs', 'crates/core/app/src/app/host.rs']:", "for relative in ['crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs']:")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source PermanentWriter::prepare program checks Ready, actual application height and reader lock, then calls the exact source Store::prepare on accepted inputs, stage_boundary on the resulting insertion transition and Storage::prepare_commit on the observed staged state before assigning Prepared. Whole success derives every prior call and all intermediate observed outputs, the single Prepared phase, the original exact accepted input order and returned insertion boundary/application root. Failure preserves the original writer phase, without asserting rollback of disposable state or physical progress. Whole successful block/freeze handoff derives globally distinct/32768-bounded concatenated inputs, including a finite native enum codec wrapper using coherence-restricted restoration and Sealed ghost membership; no universal arbitrary-Pending native codec premise. Fourteen complete reports (seven data/program definitions and seven proofs), finite guards unchanged. Source stage_boundary/application batch/Clone/ownership/async/native height/lock/type/refinement and prepared batch content remain explicit interfaces. No durable intent, participant commit, recovery/native test/control or full Transfer certification credit.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['PermanentWriter Ready/Prepared/Sealed/Interrupted phases and prepare call order modeled with unavailable Option results, not first-error labels or asynchronous traces. Stage-boundary callback takes the exact independently prepared transition and the owned state; application preparation observes its returned state and root. Native staged batch content and object/clone/Arc/lock/phase/async/owner correspondence remain explicit. No writer seal/persist_intent/commit/discard/recovery operation is modeled here; failure phase preservation does not assert rollback of disposable state or durability.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_DEFAULT_OPEN_BLOCK_WALK_AND_ONE_SHOT_SEAL_DERIVE_FROZEN_GLOBAL_INPUTS','SOURCE_WRITER_PREPARE_CALL_ORDER_PHASE_AND_EXACT_FINITE_BLOCK_INPUT_HANDOFF')
s=s.replace('BLOCK_SEAL_JOIN_COMPLETE_FORTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WRITER_PREPARE_SOURCE_COMPLETE_FORTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 5, 'inherited_audits': 425", "'fresh_audits': 14, 'inherited_audits': 459")
s=s.replace('complete forty-three-module owned root','complete forty-seven-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source writer preparation call-order/phase proof and whole finite pending codec block handoff. No desired intermediate callback success or universal arbitrary-Pending codec premise. Physical/audit guards unchanged.'"+s[end:]
s=s.replace('Autonomous serial narrow current-volume overlay source proof','Autonomous serial narrow source writer preparation proof')
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':14,'inherited_audits':459,'owned_modules':47})
