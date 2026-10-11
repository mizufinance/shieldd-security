"""Join native-only default block walk to actual sealed publication using one reached getter."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists() and not (ROOT/'handwritten').exists()
original=(DIAG/'transfer-native-seal-transfer-20261011-03/handwritten/TransferNativeSealTransfer01.lean').read_text()
start=original.index('theorem whole_bounded_publication_transfers_native_sealed_exact_global_input_vector')
end=original.index('\nset_option pp.all',start)
theorem=original[start:end]
theorem=theorem.replace('whole_bounded_publication_transfers_native_sealed_exact_global_input_vector','whole_native_only_default_block_publishes_exact_global_native_sealed_inputs',1)
a='''    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) TransferCurrentPendingReplay01.emptyPending))'''
b='''    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))'''
assert theorem.count(a)==1;theorem=theorem.replace(a,b)
a='''    (walked : TransferBlockPendingSequence01.walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final)'''
b='''    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final)'''
assert theorem.count(a)==1;theorem=theorem.replace(a,b)
a='''    (typedGetter : ∀ native, nativeSupported native = true → io.ending.decodePending (.inl (encodeNative native)) = restore native)'''
b='''    (typedGetter : io.ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)))'''
assert theorem.count(a)==1;theorem=theorem.replace(a,b)
prefix='''  have emptyBounded : BoundedPending TransferCurrentPendingReplay01.emptyPending := by
    intro key inside
    cases inside
  have storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) TransferCurrentPendingReplay01.emptyPending) := by
    rw [TransferBoundedNativeCodec01.supported_pending_encoding_is_actual_native_branch encodeNative
      TransferCurrentPendingReplay01.emptyPending (Nat.zero_le blockCapacity) emptyBounded]
    exact storedNativeDefault
  have totalRoundtrip0 := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip
  have coherentRoundtrip0 := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip0
  have emptyRead0 : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferReachablePendingBlock01.coherent_encoded_current_derives
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
      coherentRoundtrip0 _ ⟨parent, (empty : Cache (ExtendedObject O) Unit)⟩ TransferCurrentPendingReplay01.emptyPending
      (TransferPendingSetInvariant01.empty_pending_invariant blockCapacity).1 (by simpa only [apply_empty] using storedDefault)
  have initial0 : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded0 : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact emptyBounded
  have erasedWalk := TransferNativeReachableErasure01.bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued initial0 bounded0 nativeInputs
  have walked : TransferBlockPendingSequence01.walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final := erasedWalk.trans walkedNative
'''
anchor='  have nativeFinal :=';assert theorem.count(anchor)==1;theorem=theorem.replace(anchor,prefix+anchor)
start=theorem.index('  have supported : nativeSupported');end=theorem.index('  have exactTakenInputs',start)
theorem=theorem[:start]+theorem[end:]
theorem=theorem.replace('typedGetter (.sealed (allInputs requests)) supported','typedGetter')
theorem=theorem.replace('have actualObject := actual_finalization_transfer_preserves_supported_native_sealed_pending_object', 'have actualObject := TransferNativeSealTransfer01.actual_finalization_transfer_preserves_supported_native_sealed_pending_object')
header='''import ShielddSecurity.TransferNativeReachableErasure01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeOnlyPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject BoundedPending nativeSupported nullifierModulus)
open TransferPendingSetInvariant01 (Invariant)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request parentPending allInputs)
/-! Actual native-only source default object and block walk join to the exact
global sealed object/accepted vector/application root/physical recovered
boundary of the ordinary source publication pipeline. The ghost-extended
encoder walk is derived equal, not supplied. Ending getter correspondence is
only at the single actual canonical sealed enum; no universal ghost-state or
all-supported-native getter premise. Actual reached finalization field,
supported native roundtrip, canonical input projection, exact current state,
source callbacks/typed keys/Clone/snapshot/ownership/OS remain interfaces.
Same extended object type persists; this is model composition, not native
Rust trace or full certification. -/
'''
source=header+theorem+'''\nset_option pp.all true in
#check @whole_native_only_default_block_publishes_exact_global_native_sealed_inputs
#print axioms whole_native_only_default_block_publishes_exact_global_native_sealed_inputs
end ShielddSecurity.TransferNativeOnlyPublication01
'''
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferNativeOnlyPublication01.lean').write_text(source)
s=(DIAG/'transfer-native-reachable-erasure-20261011-03/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-native-delivery-erasure-20261011-01'", "UPSTREAM = DIAG / 'transfer-native-reachable-erasure-20261011-03'")
replace("POOL = DIAG / 'transfer-native-reachable-erasure-owned-floor-20261011-03'", "POOL = DIAG / 'transfer-native-only-publication-owned-floor-20261011-01'")
replace("MODULE = 'TransferNativeReachableErasure01'", "MODULE = 'TransferNativeOnlyPublication01'")
s=s.replace("'runs/01-TransferNativeDeliveryErasure01/stdout.txt'", "'runs/01-TransferNativeReachableErasure01/stdout.txt'",1)
replace("records.append(('TransferNativeDeliveryErasure01'", "records.append(('TransferNativeReachableErasure01'")
replace("    'handwritten/TransferNativeDeliveryErasure01.lean', 'project/ShielddSecurity/TransferNativeDeliveryErasure01.lean']]", "    'handwritten/TransferNativeReachableErasure01.lean', 'project/ShielddSecurity/TransferNativeReachableErasure01.lean']]")
replace('assert len(records) == 76 and len(audits) == 733','assert len(records) == 77 and len(audits) == 737')
replace("'objects': 76", "'objects': 77")
s=s.replace('seventy-six-module','seventy-seven-module').replace('733 inherited','737 inherited')
replace("'imports': ['ShielddSecurity.TransferNativeDeliveryErasure01']", "'imports': ['ShielddSecurity.TransferNativeReachableErasure01']")
replace('assert len(names) == 4','assert len(names) == 1')
replace("'fresh_audits': 4", "'fresh_audits': 1")
start=s.index('\nmapping = ');end=s.index('\ndomain = ',start)
scope='Actual native default enum pending object and native-only source block walk derive the equal ghost-extended walk under supported roundtrip/canonical input projection/key injection. Whole actual ordinary source finalization/transfer/prepare/seal/commit/recovery composes to exact global native Sealed input vector, Nodup/cap/canonical field bounds, same Frozen accepted vector/application root/Ready/Idle/final physical roots and boundary. Ending typed getter contract needed only at the single actual sealed enum; no all-supported-native or ghost-state getter equality. Actual reached finalization field correspondence remains pointwise. One complete theorem, no definitions. Same ExtendedObject type/decoder/source callbacks remain; model composition only, native Rust trace/codec/field bytes/input/library/snapshot/ICS23/ownership/temporal/locks/OS remain explicit interfaces. Zero native/control/certification credit.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh native-only whole publication capstone derives equal accepted source walk and narrows getter correspondence to the single actual sealed object. New theorem premises intentionally differ from prior nativeSeal capstone; old source/proofs immutable and reused. Qualified reachable03 four full reports reused on complete 737-report/77-module ancestry without replay. Historical failures retained; physical/per-run guards unchanged.'"+s[end:]
s=s.replace('SOURCE_BOUNDED_NATIVE_PENDING_GHOST_ERASURE_ACTUAL_STEP_AND_WHOLE_WALK','SOURCE_NATIVE_ONLY_DEFAULT_WALK_SINGLE_REACHED_GETTER_WHOLE_PUBLICATION')
s=s.replace('NATIVE_REACHABLE_ERASURE_COMPLETE_SEVENTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NATIVE_ONLY_PUBLICATION_COMPLETE_SEVENTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'inherited_audits': 733", "'inherited_audits': 737")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':1,'inherited_reports':737,'owned_modules':77,'getter_only_actual_sealed_enum':True})
