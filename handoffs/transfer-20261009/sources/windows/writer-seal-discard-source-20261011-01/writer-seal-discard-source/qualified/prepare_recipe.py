"""Prepare source writer seal/discard and actual committed/status gates."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-writer-prepare-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-reachable-pending-block-20261011-03'", "UPSTREAM = DIAG / 'transfer-writer-prepare-source-20261011-02'")
replace("POOL = DIAG / 'transfer-writer-prepare-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-writer-seal-discard-source-owned-floor-20261011-02'")
replace("MODULE = 'TransferWriterPrepareSource01'", "MODULE = 'TransferWriterSealDiscardSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferReachablePendingBlock01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferWriterPrepareSource01/stdout.txt'")
replace("records.append(('TransferReachablePendingBlock01'", "records.append(('TransferWriterPrepareSource01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generate.py', 'regeneration.json', 'generated/TransferReachablePendingBlock01.lean', 'project/ShielddSecurity/TransferReachablePendingBlock01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'repair_recipe.py', 'handwritten/TransferWriterPrepareSource01.lean', 'project/ShielddSecurity/TransferWriterPrepareSource01.lean']]")
replace('assert len(current) == 7','assert len(current) == 14')
replace('assert len(records) == 47 and len(audits) == 459','assert len(records) == 48 and len(audits) == 473')
replace("'objects': 47", "'objects': 48")
s=s.replace('Complete forty-seven-module first owned root; 459 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-eight-module first owned root; 473 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 14','assert len(names) == 13')
replace("'imports': ['ShielddSecurity.TransferReachablePendingBlock01']", "'imports': ['ShielddSecurity.TransferWriterPrepareSource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source writer seal sets Interrupted before the write lock/persist_intent call and reaches Sealed only on actual success, preserving the same frozen insertion/application/previous/next values. Wrong starting phases refuse and restore their original phase. Failed prepared seal leaves owner committed/status unavailable without asserting rollback of physical or disposable progress. Discard accepts Prepared only, restores previous Ready boundary, and refuses Sealed while retaining the previous committed boundary. Source status first obtains actual committed boundary and compares both nullifier and application-root fields before invoking its independent reader callback; Interrupted owner status is unavailable regardless of raw reader outcome. Whole successful writer prepare then seal retains exactly the same frozen accepted inputs and prepared returned boundary, deriving lock/persist success. Thirteen reports (five data/program definitions, eight proofs), source owner phase/call/equality/Clone/native lock/I/O/refinement and underlying reader/session/proof/physical durability interfaces remain explicit. No Store::persist_intent durability implementation, commit/recovery/native testing/semantic control/full Transfer certification credit.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source PermanentWriter::seal/discard/committed/status ordering and phase behavior modeled; Bool persistIntent denotes observed returned success only, not independently proved file/directory/intent durability. Failure does not imply absence or rollback of physical progress. Interrupted owner status refusal precedes the reader callback and does not assert raw Store reader refusal. Native fixed byte roots/nullifiers, struct Eq/Clone, lock/async/owner/scheduling and actual I/O effect semantics remain source refinement interfaces.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_WRITER_PREPARE_CALL_ORDER_PHASE_AND_EXACT_FINITE_BLOCK_INPUT_HANDOFF','SOURCE_WRITER_SEAL_DISCARD_COMMITTED_AND_OWNER_STATUS_GATES')
s=s.replace('WRITER_PREPARE_SOURCE_COMPLETE_FORTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WRITER_SEAL_DISCARD_SOURCE_COMPLETE_FORTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 14, 'inherited_audits': 459", "'fresh_audits': 13, 'inherited_audits': 473")
s=s.replace('complete forty-seven-module owned root','complete forty-eight-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source writer seal/discard/committed/status branch and successful same-frozen input handoff proofs. Physical progress/durability and raw reader refusal not inferred from owner phase failure. Guards unchanged.'"+s[end:]
anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_seal_discard = DIAG / 'transfer-writer-seal-discard-source-20261011-01'\nplan['pins'] += [pin(failed_seal_discard / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterSealDiscardSource01.lean', 'project/ShielddSecurity/TransferWriterSealDiscardSource01.lean', 'runs/01-TransferWriterSealDiscardSource01/stdout.txt']]\nfailed_object = failed_seal_discard / 'project/ShielddSecurity/TransferWriterSealDiscardSource01.olean'\nif failed_object.exists(): plan['pins'].append(pin(failed_object))\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\n"+s[pos:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_audits':473,'owned_modules':48})
