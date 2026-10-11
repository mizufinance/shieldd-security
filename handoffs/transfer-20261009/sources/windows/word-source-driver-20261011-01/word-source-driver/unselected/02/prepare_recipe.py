"""Construct the complete source driver using the proved typed word-field codec."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT/'prepare.py').exists()
old = DIAG/'transfer-word-object-codec-20261011-01'
s = (old/'prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
for a,b in [
 ("UPSTREAM = DIAG / 'transfer-canonical-word-pending-20261011-03'", "UPSTREAM = DIAG / 'transfer-word-object-codec-20261011-01'"),
 ("POOL = DIAG / 'transfer-word-object-codec-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-word-source-driver-owned-floor-20261011-02'"),
 ("MODULE = 'TransferWordObjectCodec01'", "MODULE = 'TransferWordSourceDriver01'"),
 ('len(records) == 118 and len(audits) == 1023','len(records) == 119 and len(audits) == 1031'),
 ("'objects': 118", "'objects': 119"),
 ('len(names) == 8','len(names) == 5'),
 ("'fresh_audits': 8, 'inherited_audits': 1023", "'fresh_audits': 5, 'inherited_audits': 1031"),
 ('WORD_OBJECT_CODEC_COMPLETE_ONE_HUNDRED_EIGHTEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'WORD_SOURCE_DRIVER_COMPLETE_ONE_HUNDRED_NINETEEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')]:
    replace(a,b)
replace("'imports': ['ShielddSecurity.TransferCanonicalWordPending01']", "'imports': ['ShielddSecurity.TransferWordObjectCodec01']")
start=s.index("stdout = UPSTREAM / ");end=s.index('assert len(records)',start)
s=s[:start]+s[start:end].replace('TransferCanonicalWordPending01','TransferWordObjectCodec01')+s[end:]
s=s.replace('one-hundred-eighteen-module','one-hundred-nineteen-module').replace('1023 inherited full reports','1031 inherited full reports')
scope = ('Whole returned source driver constructs the successful request walk and executes its reached state with source-ordered known finalization. Typed word-field pending/object codec is instantiated directly: actual successful empty-start walk derives canonical bounded global inputs, yielding concrete getter correspondence without supplied codec/getter/domain/final-object premises. Exact ordered typed mathematical source vector, supported sealed word object, frozen accepted insertions, same application root, Ready/Idle physical roots and committed boundary follow from returned root success. Five audited declarations: two definitions and three theorems. Native imbl/private Scalar/Any/downcast/Clone/primitive/compiler/Choice/CtOption/full callee/value/trace/ownership/OS bindings and older extended ghost carrier remain explicit. No ancestor replay; zero native/control/certification credit; full Transfer OPEN.')
start=s.index('\nmapping = ')
end=s.index("\nmapping['scalar_decode_source_shape']",start)
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()), 'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"], 'scope': "+repr(scope)+"}\n"+s[end:]
start=s.index("plan['source_repairs'] = ");end=s.index('\n',start)
s=s[:start]+"plan['source_repairs'] = "+repr(scope)+s[end:]
s=s.replace("plan['artifact_policy'] =", "unrunDriver = DIAG/'transfer-word-source-driver-20261011-01'\nassert not (unrunDriver/'events.jsonl').exists() and not (unrunDriver/'plan.json').exists()\nplan['pins'] += [pin(unrunDriver/n) for n in ['prepare_recipe.py','prepare.py','handwritten/TransferWordSourceDriver01.lean']]\nplan['artifact_policy'] =")
(ROOT/'prepare.py').write_text(s)

source=(DIAG/'transfer-source-ordered-driver-20261011-01/handwritten/TransferSourceOrderedDriver01.lean').read_text()
source=source.replace('import ShielddSecurity.TransferSourceOrderedFinalizer01','import ShielddSecurity.TransferWordObjectCodec01')
source=source.replace('TransferSourceOrderedDriver01','TransferWordSourceDriver01')
source=source.replace('open TransferTaggedCodecPublication01 (TaggedObject encodePending decodePending OtherFinalizationWrites liftWrites)', 'open TransferTaggedCodecPublication01 (OtherFinalizationWrites)\nopen TransferWordObjectCodec01 (WordTaggedObject encodeNative decodeNative liftWordWrites)')
source=source.replace('TaggedObject Other','WordTaggedObject Other').replace('encodePending','encodeNative').replace('decodePending','decodeNative').replace('liftWrites','liftWordWrites')
# Preserve the actual API field name while changing its codec value.
source=source.replace('ending.decodeNative','ending.decodePending').replace('with decodeNative :=','with decodePending :=')
start=source.index('/-!');end=source.index('-/',start)+2
source=source[:start]+'/-! '+scope+' -/'+source[end:]
helper='''
theorem successful_fresh_word_walk_derives_exact_sealed_codec_domain {Other E K X Tree A : Type}
    (requests : List (Request (ExtendedObject (WordTaggedObject Other)) E K X Tree A))
    (parent : State (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (final : State (ExtendedObject (WordTaggedObject Other)) × List A)
    (absent : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = none)
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walkedNative : walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued requests = some final) :
    (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs requests, key < nullifierModulus) := by
  have supportedRoundtrip := TransferWordObjectCodec01.supported_word_object_codec_restores_exact_pending_observations (Other := Other)
  have totalRoundtrip := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts
    (encodeNative (Other := Other)) decodeNative supportedRoundtrip
  have coherentRoundtrip := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip
  have emptyRead : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferCurrentPendingReplay01.current_object_absence_derives_default
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) (keyCode TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache (ExtendedObject (WordTaggedObject Other)) Unit)⟩ (by simpa only [apply_empty] using absent)
  have initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent) := by
    rw [emptyRead]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent) := by
    rw [emptyRead]
    intro key inside
    cases inside
  have erasedWalk := TransferNativeReachableErasure01.bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
    encodeNative decodeNative supportedRoundtrip keyCode TransferInjectiveKeyPublication01.keyCode_is_injective
    requests parent queued initial bounded nativeInputs
  have walked : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued requests = some final := erasedWalk.trans walkedNative
  have order := TransferReachablePendingBlock01.empty_start_reachable_walk_derives_global_inputs
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final emptyRead walked
  exact ⟨order.2.2.1, order.2.2.2.1,
    TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs⟩

'''
at=source.index('theorem fresh_absent_source_finalization_')
source=source[:at]+helper+source[at:]
source=source.replace('  have getter : io.ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) := rfl', '''  have domain := successful_fresh_word_walk_derives_exact_sealed_codec_domain requests parent queued final absent nativeInputs walkedNative
  have getter : io.ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) :=
    TransferWordObjectCodec01.canonical_bounded_sealed_word_object_getter_recovers_exact_ordered_pending (Other := Other)
      (allInputs requests) domain.2.1 domain.2.2''')
source=source.replace('(fun native _ => TransferTaggedCodecPublication01.tagged_pending_restore_roundtrip native)', '(fun native supported => TransferWordObjectCodec01.supported_word_object_codec_restores_exact_pending_observations native supported)')
at=source.index('set_option pp.all true in\n#check @fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector')
source=source[:at]+'''set_option pp.all true in
#check @successful_fresh_word_walk_derives_exact_sealed_codec_domain
#print axioms successful_fresh_word_walk_derives_exact_sealed_codec_domain
'''+source[at:]
assert 'TaggedCodecPublication01.tagged_pending' not in source
assert source.count('have domain :=')==1
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferWordSourceDriver01.lean').write_text(source)
print({'prepared_source_driver':True,'declarations':5,'guards_unchanged':True})
