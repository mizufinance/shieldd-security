import ShielddSecurity.TransferStatement

set_option maxHeartbeats 200000

namespace ShielddSecurity.RuntimeTransferStatement

-- Generated from the closed AST extraction; extraction and role interpretation
-- are reviewed trust boundaries. This checks the complete ordered field list,
-- not Rust semantics, byte canonicality, or a hash/circuit correspondence.
def rustProjection {F : Type} (s : TransferStatement F) : List F :=
  [s.rkX, s.rkY, s.anchor, s.recipientNote, s.recipientRecovery, s.changeNote, s.changeRecovery, s.balanceX, s.balanceY, s.recipientRouting, s.changeRouting, s.routingParameters, s.volumeNullifier, s.volumeCommitment, s.volumeDayStart, s.volumeContext, s.firstNullifier, s.secondNullifier, s.assetRoot, s.userRoot, s.detection0, s.detection1, s.detection2, s.detection3, s.senderCoreEpkX, s.senderCoreEpkY, s.senderCoreC2, s.senderCoreCiphertext, s.senderExtEpkX, s.senderExtEpkY, s.senderExtC2, s.senderExtCiphertext0, s.senderExtCiphertext1, s.senderExtCiphertext2, s.outputCoreEpkX, s.outputCoreEpkY, s.outputCoreC2, s.outputCoreCiphertext, s.outputExtEpkX, s.outputExtEpkY, s.outputExtC2, s.outputExtCiphertext0, s.outputExtCiphertext1, s.outputExtCiphertext2, s.timestamp, s.senderCoreConfirmation, s.outputCoreConfirmation, s.ringId, s.policyId, s.resource, s.permission, s.senderCoreSalt, s.senderExtSalt, s.outputCoreSalt, s.outputExtSalt, s.auditEpoch, s.senderOwnershipRX, s.senderOwnershipRY, s.senderOwnershipCX, s.senderOwnershipCY, s.recipientOwnershipRX, s.recipientOwnershipRY, s.recipientOwnershipCX, s.recipientOwnershipCY]

theorem projection_exact {F : Type} (s : TransferStatement F) :
    rustProjection s = s.fields := by
  rfl

theorem projection_injective {F : Type} :
    Function.Injective (rustProjection (F := F)) := by
  intro a b same
  exact TransferStatement.fields_injective
    ((projection_exact a).symm.trans (same.trans (projection_exact b)))

#print axioms projection_exact
#print axioms projection_injective

end ShielddSecurity.RuntimeTransferStatement
