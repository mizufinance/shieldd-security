"""Support fresh absent pending cache start without fabricating a stored empty object."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
tagged=(DIAG/'transfer-tagged-codec-publication-20261011-01/handwritten/TransferTaggedCodecPublication01.lean').read_text()
source=tagged[:tagged.index('/-!')].replace('import ShielddSecurity.TransferNativeGetterPublication01','import ShielddSecurity.TransferTaggedCodecPublication01').replace('namespace ShielddSecurity.TransferTaggedCodecPublication01','namespace ShielddSecurity.TransferAbsentStartPublication01')
source+='''open TransferTaggedCodecPublication01 (TaggedObject encodePending decodePending OtherFinalizationWrites liftWrites installTaggedIo)
open TransferBlockPendingSequence01 (step walk)
/-! Initial absent pending cache reads as default empty pending. Generic bounded
walk induction needs no initial stored object; nil preserves absence until
the concrete finalizer seals the empty vector. Fresh-parent constructor gives
an absent pending slot while retaining V/NV and other object observations.
Whole tagged source publication derives the exact mathematical vector and
physical boundary without caller stored-empty-object/codec/getter/frame/key
proofs. Native fresh snapshot/cache constructor, Any/Clone/selectors/full
trace/ownership/OS correspondence remains explicit; source model only. -/

def freshParent {O : Type} (verifiable nonverifiable : View Bytes) (otherObjects : View O) : State O :=
  ⟨verifiable, nonverifiable, fun key => if key = keyCode TransferNullifierObjectKeys01.nullifierBytes then none else otherObjects key⟩

'''
bounded=(DIAG/'transfer-bounded-native-codec-20261011-02/handwritten/TransferBoundedNativeCodec01.lean').read_text()
start=bounded.index('theorem successful_bounded_walk_never_stores_unsupported_pending_ghost');end=bounded.index('\ntheorem bounded_whole_input_vector_',start)
t=bounded[start:end].replace('successful_bounded_walk_never_stores_unsupported_pending_ghost','symbolic_bounded_walk_preserves_invariant_and_domain_without_initial_object',1)
a='    (storedNative : ∃ object, parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object))\n';assert t.count(a)==1;t=t.replace(a,'')
a='      BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) ∧\n      ∃ object, final.1.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl object) := by'
b='      BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) := by';assert t.count(a)==1;t=t.replace(a,b)
t=t.replace('exact ⟨initial, bounded, storedNative⟩','exact ⟨initial, bounded⟩').replace('⟨nextInvariant, nextBounded, stored⟩','⟨nextInvariant, nextBounded, _⟩').replace('nextInvariant nextBounded ⟨_, stored⟩','nextInvariant nextBounded')
t=t.replace(':= successful_bounded_whole_step_stores_supported_native_pending', ':= TransferBoundedNativeCodec01.successful_bounded_whole_step_stores_supported_native_pending')
source+=t+'\n'
nativeOnly=(DIAG/'transfer-native-only-publication-20261011-01/handwritten/TransferNativeOnlyPublication01.lean').read_text()
start=nativeOnly.index('theorem whole_native_only_default_block_publishes_exact_global_native_sealed_inputs');end=nativeOnly.index('\nset_option pp.all true in',start)
t=nativeOnly[start:end];head,_=t.split(' := by\n',1)
head=head.replace('whole_native_only_default_block_publishes_exact_global_native_sealed_inputs','whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs',1)
a='    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =\n      some (.inl (encodeNative (.opened [] []))))';assert head.count(a)==1
head=head.replace(a,'    (absent : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = none)')
body='''  have emptyBounded : BoundedPending TransferCurrentPendingReplay01.emptyPending := by
    intro key inside
    cases inside
  have totalRoundtrip0 := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip
  have coherentRoundtrip0 := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip0
  have emptyRead0 : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferCurrentPendingReplay01.current_object_absence_derives_default
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) (project TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache (ExtendedObject O) Unit)⟩ (by simpa only [apply_empty] using absent)
  have initial0 : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded0 : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact emptyBounded
  have erasedWalk := TransferNativeReachableErasure01.bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued initial0 bounded0 nativeInputs
  have walked : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final := erasedWalk.trans walkedNative
  have nativeFinal := symbolic_bounded_walk_preserves_invariant_and_domain_without_initial_object
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final initial0 bounded0 nativeInputs walked
'''
rest=t[t.index('  have order :='):]
rest=rest.replace('coherentRoundtrip project injection','coherentRoundtrip0 project injection').replace('final emptyRead walked','final emptyRead0 walked').replace('exact nativeFinal.2.1','exact nativeFinal.2')
source+=head+' := by\n'+body+rest+'\n'
start=tagged.index('theorem tagged_codec_source_finalization_publishes_exact_global_mathematical_input_vector');end=tagged.index('\nset_option pp.all true in',start)
t=tagged[start:end];head,_=t.split(' := by\n',1)
head=head.replace('tagged_codec_source_finalization_publishes_exact_global_mathematical_input_vector','fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector',1)
a='(parent : State (ExtendedObject (TaggedObject Other)))';assert head.count(a)==1
head=head.replace(a,'(verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other)))')
start=head.index('    (storedNativeDefault : ');end=head.index('    (walkedNative : ',start);head=head[:start]+head[end:]
head=re.sub(r'\bparent\b','(freshParent verifiable nonverifiable otherObjects)',head)
body='''  let requests := installRequests inputs wordOf sourceRequests
  let parent := freshParent verifiable nonverifiable otherObjects
  let io := installTaggedIo writesOf baseIo
  have sourceProjection := TransferInstalledSourcePublication01.installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests
  have nativeInputs := TransferTypedScalarPublication01.typed_action_projection_derives_canonical_native_input_bounds
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  have absent : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = none := by
    simp only [parent, freshParent, ite_true]
  have getter : io.ending.decodePending (.inl (encodePending (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) := rfl
  have frame := TransferKnownFinalizerPublication01.installed_known_finalizer_derives_reached_publication_field_frame
    (encodePending (Other := Other)) (decodePending (Other := Other)) keyCode TransferInjectiveKeyPublication01.keyCode_is_injective
    (fun height state queued => TransferFixedFinalizerPublication01.toEffects (liftWrites (writesOf height state queued)))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodePending)}}
    host height final.2
  have values := TransferTypedScalarPublication01.global_source_input_vector_is_exact_typed_montgomery_projection
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  refine ⟨values.trans ?_, ?_⟩
  · exact congrArg (fun words : List (Vector UInt64 4) => words.map montgomeryValue)
      (TransferInstalledSourcePublication01.installed_request_batch_retains_exact_ordered_source_word_vector inputs wordOf sourceRequests)
  · exact whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs
      (encodePending (Other := Other)) (decodePending (Other := Other))
      (fun native _ => TransferTaggedCodecPublication01.tagged_pending_restore_roundtrip native)
      keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final absent nativeInputs walkedNative
      io host height root currentState rfl getter frame success
'''
source+=head+' := by\n'+body
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==4
for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
source+='end ShielddSecurity.TransferAbsentStartPublication01\n'
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferAbsentStartPublication01.lean').write_text(source)
s=(DIAG/'transfer-tagged-codec-publication-20261011-01/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-getter-publication-20261011-01'", "UPSTREAM = DIAG / 'transfer-tagged-codec-publication-20261011-01'")
replace("POOL = DIAG / 'transfer-tagged-codec-publication-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-absent-start-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferTaggedCodecPublication01'", "MODULE = 'TransferAbsentStartPublication01'")
replace("stdout = UPSTREAM / 'runs/01-TransferNativeGetterPublication01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferTaggedCodecPublication01/stdout.txt'")
replace('assert len(current) == 3','assert len(current) == 8')
replace("records.append(('TransferNativeGetterPublication01'", "records.append(('TransferTaggedCodecPublication01'")
replace("    'handwritten/TransferNativeGetterPublication01.lean', 'project/ShielddSecurity/TransferNativeGetterPublication01.lean']]", "    'handwritten/TransferTaggedCodecPublication01.lean', 'project/ShielddSecurity/TransferTaggedCodecPublication01.lean']]")
replace('assert len(records) == 98 and len(audits) == 897','assert len(records) == 99 and len(audits) == 905')
replace("'objects': 98", "'objects': 99")
s=s.replace('ninety-eight-module','ninety-nine-module').replace('897 inherited','905 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeGetterPublication01']", "'imports': ['ShielddSecurity.TransferTaggedCodecPublication01']")
replace('assert len(names) == 8','assert len(names) == 4');replace("'fresh_audits': 8", "'fresh_audits': 4")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Initial absent pending cache reads default empty. Symbolic bounded native-model walk preserves invariant/domain without any initial object existence; nil may keep absence until finalizer seals empty vector. Fresh parent constructor has absent pending slot and retains V/NV/other object observations. Whole tagged source publication derives exact ordered mathematical nullifiers/native sealed object/accepted inputs/application root/Ready writer/Idle Host/physical recovered boundary. Four complete reports: one definition/three theorems. No caller initial stored-empty-object/codec/getter/source projection/key-injection/final field frame supplied to fresh whole theorem. Native fresh snapshot/cache constructor/Any/Clone/selectors/full trace/ownership/OS bindings remain explicit; old extended ghost carrier persists. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace('TAGGED_CODEC_PUBLICATION_COMPLETE_NINETY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','ABSENT_START_PUBLICATION_COMPLETE_NINETY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN').replace("'inherited_audits': 897", "'inherited_audits': 905")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_reports':905,'owned_modules':99,'full_native_trace_still_open':True})
