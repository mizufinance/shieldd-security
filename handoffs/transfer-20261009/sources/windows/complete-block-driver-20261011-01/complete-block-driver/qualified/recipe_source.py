"""Compose native-only source walk and reached host assignment into returned block program."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
old=(DIAG/'transfer-absent-start-publication-20261011-01/handwritten/TransferAbsentStartPublication01.lean').read_text()
source=old[:old.index('/-!')].replace('import ShielddSecurity.TransferTaggedCodecPublication01','import ShielddSecurity.TransferAbsentStartPublication01').replace('namespace ShielddSecurity.TransferAbsentStartPublication01','namespace ShielddSecurity.TransferCompleteBlockDriver01')
source+='''open TransferAbsentStartPublication01 (freshParent)
/-! Returned whole-block source model explicitly composes native-only action
walk from fresh absent pending cache, assigns its reached state to the Host,
then executes concrete tagged-codec/fixed-finalizer publication. A returned
root derives the actual walk/reached state and complete publication witness;
caller walk-result and host-current-state equalities are eliminated.
None means no modeled whole return, with no failure-prefix/rollback claim.
Native loop/Host ownership/fresh cache/selectors/full component trace/library/
snapshot/OS correspondence remains explicit; zero native/certification credit. -/

def runCompleteBlock {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other))) (height : Fin (2 ^ 64)) :
    Option (TransferEndToEnd01.Outcome (ExtendedObject (TaggedObject Other)) A) :=
  (walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
    (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode
    (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests)).map
    (fun final => TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2)

theorem returned_whole_block_derives_actual_walk_exact_inputs_and_publication {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (TaggedObject Other)) A) (root : Nat)
    (returned : runCompleteBlock inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    ∃ final : State (ExtendedObject (TaggedObject Other)) × List A,
      walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
        (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode
        (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) = some final ∧
      outcome = TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2 ∧
      allInputs (installRequests inputs wordOf sourceRequests) =
        (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
      ∃ state,
        (TransferHostEndBlock01.transferred (installTaggedIo writesOf baseIo).ending {host with active := final.1} height final.2).returned = some state ∧
        state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
          some (.inl (encodePending (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
        (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧
        (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
        (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
        ∃ (frozen : TransferWriterPrepareSource01.Frozen),
          frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
          outcome.host.writer = .ready frozen.next ∧ outcome.host.phase = .idle ∧
          outcome.host.store.actualRoots = frozen.next.nullifiers.roots ∧ outcome.host.store.boundary = some frozen.next.nullifiers := by
  cases ran : walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
      (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode
      (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) with
  | none =>
    simp only [runCompleteBlock, ran, Option.map_none] at returned
    cases returned
  | some final =>
    have same : TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2 = outcome :=
      Option.some.inj (by simpa only [runCompleteBlock, ran, Option.map_some] using returned)
    have rootSuccess : (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) {host with active := final.1} height final.2).root = some root := by
      rw [same]
      exact success
    have publication := TransferAbsentStartPublication01.fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
      inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued final ran writesOf baseIo
      {host with active := final.1} height root rfl rootSuccess
    refine ⟨final, rfl, same.symm, ?_⟩
    simpa only [same] using publication

'''
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==2
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferCompleteBlockDriver01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferCompleteBlockDriver01.lean').write_text(source)
s=(DIAG/'transfer-absent-start-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-tagged-codec-publication-20261011-01'", "UPSTREAM = DIAG / 'transfer-absent-start-publication-20261011-01'")
replace("POOL = DIAG / 'transfer-absent-start-publication-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-complete-block-driver-owned-floor-20261011-02'")
replace("MODULE = 'TransferAbsentStartPublication01'", "MODULE = 'TransferCompleteBlockDriver01'")
replace("stdout = UPSTREAM / 'runs/01-TransferTaggedCodecPublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferAbsentStartPublication01/stdout.txt'")
replace('assert len(current) == 8','assert len(current) == 4')
replace("records.append(('TransferTaggedCodecPublication01'", "records.append(('TransferAbsentStartPublication01'")
replace("    'handwritten/TransferTaggedCodecPublication01.lean', 'project/ShielddSecurity/TransferTaggedCodecPublication01.lean']]", "    'handwritten/TransferAbsentStartPublication01.lean', 'project/ShielddSecurity/TransferAbsentStartPublication01.lean']]")
replace('assert len(records) == 99 and len(audits) == 905','assert len(records) == 100 and len(audits) == 909')
replace("'objects': 99", "'objects': 100")
s=s.replace('ninety-nine-module','one-hundred-module').replace('905 inherited','909 inherited')
replace("'imports': ['ShielddSecurity.TransferTaggedCodecPublication01']", "'imports': ['ShielddSecurity.TransferAbsentStartPublication01']")
replace('assert len(names) == 4','assert len(names) == 2');replace("'fresh_audits': 4", "'fresh_audits': 2")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Returned whole-block source driver composes native-only all-slot typed request walk from fresh absent pending cache, assigns actual reached state to Host, and executes concrete tagged codec/getter/fixed six-key finalizer publication. Returned root derives actual walk witness, exact ordered mathematical input vector/native sealed object/accepted inputs/application root/Ready writer/Idle Host/physical recovered boundary. Two complete reports: one definition/one theorem. No caller successful walk/current Host-state identity/stored-empty-object/codec/getter/source projection/key injection/final field frame supplied. None denotes no modeled whole return, no failure-prefix/rollback claim. Native loop/Host ownership/fresh cache/selectors/full trace/library/snapshot/OS bindings remain explicit; old ghost carrier persists. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('ABSENT_START_PUBLICATION_COMPLETE_NINETY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','COMPLETE_BLOCK_DRIVER_COMPLETE_ONE_HUNDRED_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 905", "'inherited_audits': 909")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':2,'inherited_reports':909,'owned_modules':100,'full_native_trace_still_open':True})
