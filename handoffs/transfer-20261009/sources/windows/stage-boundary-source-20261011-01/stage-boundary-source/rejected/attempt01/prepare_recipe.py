"""Prepare actual transition validation, initialization gates and boundary writes."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-store-commit-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-persist-intent-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-store-commit-source-20261011-02'")
replace("POOL = DIAG / 'transfer-store-commit-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-stage-boundary-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferStoreCommitSource01'", "MODULE = 'TransferStageBoundarySource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferPersistIntentSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferStoreCommitSource01/stdout.txt'")
replace("records.append(('TransferPersistIntentSource01'", "records.append(('TransferStoreCommitSource01'")
replace("'repair_recipe.py', 'handwritten/TransferPersistIntentSource01.lean', 'project/ShielddSecurity/TransferPersistIntentSource01.lean'", "'repair_recipe.py', 'handwritten/TransferStoreCommitSource01.lean', 'project/ShielddSecurity/TransferStoreCommitSource01.lean'")
replace('assert len(current) == 10','assert len(current) == 13')
replace('assert len(records) == 51 and len(audits) == 505','assert len(records) == 52 and len(audits) == 518')
replace("'objects': 51", "'objects': 52")
s=s.replace('Complete fifty-one-module first owned root; 505 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-two-module first owned root; 518 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 13','assert len(names) == 15')
replace("'imports': ['ShielddSecurity.TransferPersistIntentSource01']", "'imports': ['ShielddSecurity.TransferStoreCommitSource01']")
replace("for relative in ['crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs']:", "for relative in ['crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs', 'crates/core/component/sct/src/permanent_nullifiers.rs']:")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source stage_boundary validates finite consecutive next height, capacity, actual duplicate loop and initial default boundary, then refuses missing/unavailable parent initialization reads or existing boundary/format/root/legacy nullifier values. Later boundary equality is checked against actual readPrevious observation. Fallible next-boundary serialization precedes exactly three verifiable writes with observed serialized next boundary, format bytes and aggregate roots commitment. Writes frame nonverifiable/object state and all other verifiable keys; separated key premises derive each exact stored value. Successful actual Store.prepare derives all transition validation with only explicit checked initial-default premise; whole writer Frozen success with installed actual stage program derives original accepted inputs, stage validation/parent gates/serialization/exact staged state and application preparation on that staged state. Fifteen reports (nine data/program definitions, six proofs), finite/physical/strict audit guards unchanged. Native fixed-width/root/blockId values, set representation, read_boundary implementation, raw getter/current view/availability, static keys, serde serialization and root commitment/Clone/owner/concurrency/batch/durability remain explicit interfaces. Height range represents native u64 domain, not extra runtime check. No native/control/full Transfer certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source stage key parameters must denote the pinned boundary/format/root and two legacy key literals through an injective native representation; their separation is explicit in exact-three-value theorem. Format and root commitment denote native FORMAT and Roots::commitment bytes; their semantic crypto/serde correspondence is not inferred from hash identity. Native raw get availability and typed immutable current view/async ownership are interfaces; parent checks do not establish native read trace or snapshot locks. ValidTransition finite height bound is native typed u64 embedding, and original uniqueLoop recurrence represents actual BTreeSet insertion success. Store.prepare lacks an initial-default check; deriving stage validation correctly requires independently checked default boundary in genesis case.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_STORE_COMMIT_ORDERED_PARTICIPANTS_OBSERVED_ROOTS_AND_BLOCKED_READINESS','SOURCE_STAGE_BOUNDARY_VALIDATION_PARENT_GATES_AND_EXACT_WRITES')
s=s.replace('STORE_COMMIT_SOURCE_COMPLETE_FIFTY_ONE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','STAGE_BOUNDARY_SOURCE_COMPLETE_FIFTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 13, 'inherited_audits': 505", "'fresh_audits': 15, 'inherited_audits': 518")
s=s.replace('complete fifty-one-module owned root','complete fifty-two-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source validation/initialization/actual staged state and writer application preparation join; no ancestors replayed. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':15,'inherited_audits':518,'owned_modules':52})
