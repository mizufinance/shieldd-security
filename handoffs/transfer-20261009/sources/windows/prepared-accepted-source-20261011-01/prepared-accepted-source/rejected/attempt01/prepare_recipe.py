"""Prepare frozen complete block inputs joined to source Store::prepare gates."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-block-seal-join-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-pending-seal-source-20261011-03'", "UPSTREAM = DIAG / 'transfer-block-seal-join-20261011-01'")
replace("POOL = DIAG / 'transfer-block-seal-join-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-prepared-accepted-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferBlockSealJoin01'", "MODULE = 'TransferPreparedAcceptedSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferPendingSealSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferBlockSealJoin01/stdout.txt'")
replace("records.append(('TransferPendingSealSource01'", "records.append(('TransferBlockSealJoin01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingSealSource01.lean', 'project/ShielddSecurity/TransferPendingSealSource01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferBlockSealJoin01.lean', 'project/ShielddSecurity/TransferBlockSealJoin01.lean']]")
replace('assert len(current) == 13','assert len(current) == 5')
replace('assert len(records) == 43 and len(audits) == 425','assert len(records) == 44 and len(audits) == 430')
replace("'objects': 43", "'objects': 44")
s=s.replace('Complete forty-three-module first owned root; 425 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-four-module first owned root; 430 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 5','assert len(names) == 10')
replace("'imports': ['ShielddSecurity.TransferPendingSealSource01']", "'imports': ['ShielddSecurity.TransferBlockSealJoin01']")
replace("for relative in ['crates/core/component/sct/src/component/sct.rs', 'crates/core/app/src/app/host.rs']:", "for relative in ['crates/core/app/src/app/permanent_writer.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs']:")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Same complete successful block walk and one-shot freeze derive exact globally distinct bounded inputs. Source Store::prepare prefix checks readiness/partition health, intent absence, capacity, BTreeSet insertion uniqueness, actual roots/current boundary and checked consecutive u64 height; on success its transition preserves the original accepted input order and uses independently observed partition roots. Nodup implies symbolic set insertion loop acceptance, so both source capacity and duplicate gates follow from the block proof without desired set-gate premises. All arbitrary prefix failure and capacity/duplicate refusal yield unavailable preparation before the partition interface. Partition key hashing/sorting/collision/read/finish/witness/verify_insertions represented by an explicit fallible sessions interface; no witness validity or native storage/correspondence/durability credit. Typed object/vector/set/native boundary representation, source phase/height/owner handoff, and full Host/Transfer remain open. No generated source edits, unsound axioms or unbounded recurrence.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Store::prepare source prefix Option refusal abstracts returned error distinctions; Gate conjoins the actual ordered prefix checks, preserving call suppression but not a first-error label or trace. BTreeSet uniqueness is modeled by the existing symbolic uniqueLoop; partitions/session/collision/read/finish/witness/verify_insertions remain explicit fallible sessions interface with observed next roots. Existing Store healthy models all partition poison flags. Native RootSet and blockId fixed lengths, concrete nullifier/Vec/BTreeSet representations and source scheduling/owner immutability remain interfaces.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_DEFAULT_OPEN_BLOCK_WALK_AND_ONE_SHOT_SEAL_DERIVE_FROZEN_GLOBAL_INPUTS','SOURCE_FROZEN_GLOBAL_INPUTS_DISCHARGE_STORE_PREPARE_CAPACITY_AND_DUPLICATE_GATES')
s=s.replace('BLOCK_SEAL_JOIN_COMPLETE_FORTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','PREPARED_ACCEPTED_SOURCE_COMPLETE_FORTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 5, 'inherited_audits': 425", "'fresh_audits': 10, 'inherited_audits': 430")
s=s.replace('complete forty-three-module owned root','complete forty-four-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source Store::prepare gates and exact accepted transition assembly, with complete block/freeze set gates derived and partition-session interfaces explicit. All physical/audit guards unchanged.'"+s[end:]
s=s.replace('Autonomous serial narrow current-volume overlay source proof','Autonomous serial narrow source frozen accepted prepare proof')
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':10,'inherited_audits':430,'owned_modules':44})
