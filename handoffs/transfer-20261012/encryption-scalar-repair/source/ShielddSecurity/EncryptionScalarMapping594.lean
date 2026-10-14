import ShielddSecurity.RemainingWordSeed369
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.EncryptionScalarMapping594
/-- Semantic identities for the six scalar columns in the pinned capture.
The runtime allocation order is ownership zero and one, then four tiers.
These lemmas check the Lean assignment; runtime source identity is separately audited. -/
theorem ownership0 (w : TransferSem.Witness) : RemainingWordSeed369.value w 8551=(w.encryption.ownership 0).randomness := by rfl
theorem ownership1 (w : TransferSem.Witness) : RemainingWordSeed369.value w 10083=(w.encryption.ownership 1).randomness := by rfl
theorem tier0 (w : TransferSem.Witness) : RemainingWordSeed369.value w 11611=(w.encryption.tiers 0).ephemeral := by rfl
theorem tier1 (w : TransferSem.Witness) : RemainingWordSeed369.value w 13629=(w.encryption.tiers 1).ephemeral := by rfl
theorem tier2 (w : TransferSem.Witness) : RemainingWordSeed369.value w 14891=(w.encryption.tiers 2).ephemeral := by rfl
theorem tier3 (w : TransferSem.Witness) : RemainingWordSeed369.value w 16153=(w.encryption.tiers 3).ephemeral := by rfl
end ShielddSecurity.EncryptionScalarMapping594

set_option pp.all true in
#check @ShielddSecurity.EncryptionScalarMapping594.ownership0
#print axioms ShielddSecurity.EncryptionScalarMapping594.ownership0

set_option pp.all true in
#check @ShielddSecurity.EncryptionScalarMapping594.ownership1
#print axioms ShielddSecurity.EncryptionScalarMapping594.ownership1

set_option pp.all true in
#check @ShielddSecurity.EncryptionScalarMapping594.tier0
#print axioms ShielddSecurity.EncryptionScalarMapping594.tier0

set_option pp.all true in
#check @ShielddSecurity.EncryptionScalarMapping594.tier1
#print axioms ShielddSecurity.EncryptionScalarMapping594.tier1

set_option pp.all true in
#check @ShielddSecurity.EncryptionScalarMapping594.tier2
#print axioms ShielddSecurity.EncryptionScalarMapping594.tier2

set_option pp.all true in
#check @ShielddSecurity.EncryptionScalarMapping594.tier3
#print axioms ShielddSecurity.EncryptionScalarMapping594.tier3
