import Mathlib.Logic.Function.Defs

set_option maxHeartbeats 200000

namespace ShielddSecurity

/-- The semantic public data of a two-input/two-output Transfer. Field values
are already decoded here: byte canonicality, curve membership, authorization,
and the meaning of ciphertexts are separate predicates, not hidden assumptions.
This specification is handwritten; correspondence with the Rust projection and
the actual statement-hash constraints requires its own checked mapping. -/
structure TransferStatement (F : Type) where
  rkX : F
  rkY : F
  anchor : F
  recipientNote : F
  recipientRecovery : F
  changeNote : F
  changeRecovery : F
  balanceX : F
  balanceY : F
  routingSlot0 : F
  routingSlot1 : F
  routingParameters : F
  volumeNullifier : F
  volumeCommitment : F
  volumeDayStart : F
  volumeContext : F
  firstNullifier : F
  secondNullifier : F
  assetRoot : F
  userRoot : F
  detection0 : F
  detection1 : F
  detection2 : F
  detection3 : F
  senderCoreEpkX : F
  senderCoreEpkY : F
  senderCoreC2 : F
  senderCoreCiphertext : F
  senderExtEpkX : F
  senderExtEpkY : F
  senderExtC2 : F
  senderExtCiphertext0 : F
  senderExtCiphertext1 : F
  senderExtCiphertext2 : F
  outputCoreEpkX : F
  outputCoreEpkY : F
  outputCoreC2 : F
  outputCoreCiphertext : F
  outputExtEpkX : F
  outputExtEpkY : F
  outputExtC2 : F
  outputExtCiphertext0 : F
  outputExtCiphertext1 : F
  outputExtCiphertext2 : F
  timestamp : F
  senderCoreConfirmation : F
  outputCoreConfirmation : F
  ringId : F
  policyId : F
  resource : F
  permission : F
  senderCoreSalt : F
  senderExtSalt : F
  outputCoreSalt : F
  outputExtSalt : F
  auditEpoch : F
  senderOwnershipRX : F
  senderOwnershipRY : F
  senderOwnershipCX : F
  senderOwnershipCY : F
  recipientOwnershipRX : F
  recipientOwnershipRY : F
  recipientOwnershipCX : F
  recipientOwnershipCY : F

namespace TransferStatement

/-- Ordered statement preimage. Point coordinates, input/output roles, policy
fields and epochs occupy separate positions; this is not an unordered set. -/
def fields {F : Type} (s : TransferStatement F) : List F :=
  [s.rkX, s.rkY, s.anchor,
   s.recipientNote, s.recipientRecovery, s.changeNote, s.changeRecovery,
   s.balanceX, s.balanceY, s.routingSlot0, s.routingSlot1,
   s.routingParameters,
   s.volumeNullifier, s.volumeCommitment, s.volumeDayStart, s.volumeContext,
   s.firstNullifier, s.secondNullifier,
   s.assetRoot, s.userRoot,
   s.detection0, s.detection1, s.detection2, s.detection3,
   s.senderCoreEpkX, s.senderCoreEpkY, s.senderCoreC2, s.senderCoreCiphertext,
   s.senderExtEpkX, s.senderExtEpkY, s.senderExtC2,
   s.senderExtCiphertext0, s.senderExtCiphertext1, s.senderExtCiphertext2,
   s.outputCoreEpkX, s.outputCoreEpkY, s.outputCoreC2, s.outputCoreCiphertext,
   s.outputExtEpkX, s.outputExtEpkY, s.outputExtC2,
   s.outputExtCiphertext0, s.outputExtCiphertext1, s.outputExtCiphertext2,
   s.timestamp, s.senderCoreConfirmation, s.outputCoreConfirmation,
   s.ringId, s.policyId, s.resource, s.permission,
   s.senderCoreSalt, s.senderExtSalt, s.outputCoreSalt, s.outputExtSalt, s.auditEpoch,
   s.senderOwnershipRX, s.senderOwnershipRY, s.senderOwnershipCX, s.senderOwnershipCY,
   s.recipientOwnershipRX, s.recipientOwnershipRY,
   s.recipientOwnershipCX, s.recipientOwnershipCY]

theorem fields_length {F : Type} (s : TransferStatement F) : s.fields.length = 64 := by
  rfl

/-- Projection itself loses no semantic field. This is stronger than counting
fields, but does not assert injectivity of the subsequent cryptographic hash. -/
theorem fields_injective {F : Type} : Function.Injective (fields (F := F)) := by
  intro a b same
  cases a
  cases b
  simpa only [fields, List.cons.injEq, and_true, TransferStatement.mk.injEq] using same

/-- Equivocation between two distinct semantic statements with equal hashes
exhibits a collision on distinct ordered preimages. No universal hash-injectivity
axiom is introduced. A computational security claim must bound this collision
event for the exact deployed construction and then establish runtime binding. -/
theorem equivocation_is_collision {F D : Type} (hash : List F → D)
    (a b : TransferStatement F) (different : a ≠ b)
    (sameHash : hash a.fields = hash b.fields) :
    a.fields ≠ b.fields ∧ hash a.fields = hash b.fields := by
  exact ⟨fun same => different (fields_injective same), sameHash⟩

#print axioms fields_length
#print axioms fields_injective
#print axioms equivocation_is_collision

end TransferStatement
end ShielddSecurity
