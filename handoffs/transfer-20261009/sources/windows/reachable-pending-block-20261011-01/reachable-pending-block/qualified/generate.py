"""Maintain the same whole programs with a coherence-restricted codec proof.

Reuses exact qualified symbolic proofs, replacing only the roundtrip premise
and its uses after coherence has independently been derived. The finite codec
wrapper requires observational native-enum correspondence, never roundtrip
of arbitrary model membership functions. Does not edit generated evidence.
"""
import re, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
sequence=(DIAG/'transfer-block-pending-sequence-20261011-01/handwritten/TransferBlockPendingSequence01.lean').read_text()
seal=(DIAG/'transfer-block-seal-join-20261011-01/handwritten/TransferBlockSealJoin01.lean').read_text()
header='''import ShielddSecurity.TransferPendingFiniteCodec01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferReachablePendingBlock01
open TransferStateDelta TransferIndexWriterModel01
open TransferNullifierBatchSource01 (Pending)
open TransferPendingSetInvariant01 (Invariant Coherent)
open TransferNullifierConsensusLimits01 (SupportedWidth blockCapacity nativeWordMax)
open TransferBlockPendingSequence01 (Request parentPending bindPending step walk allInputs)
open TransferPendingSealSource01 (sealOnce freeze ensureSealed SealError)

/-! The same source whole step/walk/freeze now uses typed codec roundtrip only
for coherent states. Successful actual inspection derives next coherence before
any roundtrip use; frozen membership is coherent by construction. The finite
enum wrapper uses order-only Sealed storage and reconstructed ghost membership,
so no arbitrary membership-function roundtrip is assumed. Primitive native
typed object embedding/Clone, finite collections, actual nullifier values,
whole program scheduling/owner, reader/crypto/Host/durability remain explicit.
No native or full Transfer certification. Finite symbolic list induction. -/

theorem coherent_encoded_current_derives {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)
    (objectKey : Nat) (child : Delta O E) (pending : Pending) (coherent : Coherent pending)
    (stored : (applyCache child.parent child.cache).objects objectKey = some (encode pending)) :
    TransferCurrentPendingReplay01.currentPending decode objectKey child = pending := by
  simp only [TransferCurrentPendingReplay01.currentPending, stored, roundtrip pending coherent]

'''
body=sequence[sequence.index('theorem whole_step_preserves_pending_invariant'):sequence.index('theorem absent_start_successful_block')]
body=body.replace('whole_step_preserves_pending_invariant','whole_step_preserves_reachable_pending_codec')
body=body.replace('successful_walk_preserves_invariant_and_exact_input_order','successful_walk_uses_only_coherent_codec')
old='(roundtrip : ∀ pending, decode (encode pending) = pending)'
new='(roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)'
assert body.count(old)==2; body=body.replace(old,new)
old_use='TransferCurrentPendingReplay01.encoded_current_object_derives_pending encode decode roundtrip _\n      ⟨committed.parent, (empty : Cache O Unit)⟩ pending (by simpa only [apply_empty] using stored)'
new_use='coherent_encoded_current_derives encode decode roundtrip _\n      ⟨committed.parent, (empty : Cache O Unit)⟩ pending invariant.1 (by simpa only [apply_empty] using stored)'
assert body.count(old_use)==1; body=body.replace(old_use,new_use)
global_proof=seal[seal.index('theorem empty_start_successful_walk_derives_global_inputs'):seal.index('theorem nonempty_successful_walk_retains_current_encoding')]
assert global_proof.count(old)==1; global_proof=global_proof.replace(old,new)
global_proof=global_proof.replace('empty_start_successful_walk_derives_global_inputs','empty_start_reachable_walk_derives_global_inputs')
global_proof=global_proof.replace('TransferBlockPendingSequence01.successful_walk_preserves_invariant_and_exact_input_order','successful_walk_uses_only_coherent_codec')
full=seal[seal.index('theorem successful_block_seals_exact_global_inputs_once_and_refuses_later_staging'):seal.index('set_option pp.all true in')]
assert full.count(old)==1; full=full.replace(old,new)
full=full.replace('successful_block_seals_exact_global_inputs_once_and_refuses_later_staging','coherent_block_seals_exact_global_inputs_and_refuses_later_staging')
full=full.replace('empty_start_successful_walk_derives_global_inputs','empty_start_reachable_walk_derives_global_inputs')
split=full.index(' :\n    let output')
proof_split=full.index(' := by\n',split)
conclusion=full[split+3:proof_split]
facts='''def BlockSealFacts {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat)
    (requests : List (Request O E K X Tree A)) (final : State O × List A) : Prop :=
'''+conclusion+'\n\n'
full=full[:split]+' :\n    BlockSealFacts encode decode project requests final'+full[proof_split:]
full=full.replace('  dsimp only\n','  dsimp only [BlockSealFacts]\n',1)
old_use='TransferCurrentPendingReplay01.encoded_current_object_derives_pending encode decode roundtrip _\n      ⟨sealedState, (empty : Cache O Unit)⟩ (freeze (parentPending decode project final.1)) (by simpa only [apply_empty] using stored)'
new_use='coherent_encoded_current_derives encode decode roundtrip _\n      ⟨sealedState, (empty : Cache O Unit)⟩ (freeze (parentPending decode project final.1))\n      (TransferPendingSealSource01.freeze_exact_order_membership_and_sealed _).2.1 (by simpa only [apply_empty] using stored)'
assert full.count(old_use)==1; full=full.replace(old_use,new_use)
old_ensure='''  · exact TransferPendingSealSource01.encoded_frozen_ensure_succeeds encode decode roundtrip _ ⟨sealedState, (empty : Cache O Unit)⟩
      (parentPending decode project final.1) (by simpa only [apply_empty] using stored)'''
new_ensure='''  · change ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ = .ok ()
    have frozenCoherent := (TransferPendingSealSource01.freeze_exact_order_membership_and_sealed (parentPending decode project final.1)).2.1
    have encodedSealed : (decode (encode (freeze (parentPending decode project final.1)))).sealed = true :=
      congrArg Pending.sealed (roundtrip (freeze (parentPending decode project final.1)) frozenCoherent)
    simp only [ensureSealed, apply_empty, stored, encodedSealed, if_true]'''
assert full.count(old_ensure)==1; full=full.replace(old_ensure,new_ensure)
wrapper='''theorem finite_codec_default_block_seals_exact_global_inputs {O E K X Tree A : Type}
    (encodeNative : TransferPendingFiniteCodec01.NativePending → O) (decodeNative : O → TransferPendingFiniteCodec01.NativePending)
    (typedRoundtrip : ∀ native, TransferPendingFiniteCodec01.restore (decodeNative (encodeNative native)) = TransferPendingFiniteCodec01.restore native)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode encodeNative TransferCurrentPendingReplay01.emptyPending))
    (success : walk (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative)
      project parent queued requests = some final) :
    BlockSealFacts (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative) project requests final := by
  have reachableRoundtrip : ∀ pending, Coherent pending →
      TransferPendingFiniteCodec01.decode decodeNative (TransferPendingFiniteCodec01.encode encodeNative pending) = pending :=
    TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending encodeNative decodeNative typedRoundtrip
  have emptyCoherent : Coherent TransferCurrentPendingReplay01.emptyPending :=
    (TransferPendingSetInvariant01.empty_pending_invariant blockCapacity).1
  have emptyStart : parentPending (TransferPendingFiniteCodec01.decode decodeNative) project parent = TransferCurrentPendingReplay01.emptyPending :=
    coherent_encoded_current_derives (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative)
      reachableRoundtrip _ ⟨parent, (empty : Cache O Unit)⟩ TransferCurrentPendingReplay01.emptyPending emptyCoherent
      (by simpa only [apply_empty] using storedDefault)
  exact coherent_block_seals_exact_global_inputs_and_refuses_later_staging (TransferPendingFiniteCodec01.encode encodeNative)
    (TransferPendingFiniteCodec01.decode decodeNative) reachableRoundtrip project injection requests parent queued final emptyStart success

'''
source=header+body+global_proof+facts+full+wrapper
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M); assert len(names)==7
source+=''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n' for n in names)
source+='end ShielddSecurity.TransferReachablePendingBlock01\n'
target=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'generated/TransferReachablePendingBlock01.lean'
assert not target.exists(); target.parent.mkdir(parents=True,exist_ok=True); target.write_text(source)
print({'generated':str(target),'audits':len(names),'global_arbitrary_pending_roundtrip':False})
