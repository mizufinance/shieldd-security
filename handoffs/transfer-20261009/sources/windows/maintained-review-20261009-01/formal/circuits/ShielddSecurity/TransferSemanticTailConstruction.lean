import ShielddSecurity.TransferOutputRecoveryCompletion
import ShielddSecurity.TransferVolumeBranchCompletion
import ShielddSecurity.TransferEncryptionBranchCompletion
import ShielddSecurity.TransferRoutingBranchCompletion
import ShielddSecurity.TransferPublicCanonicality

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferSemanticTailConstruction

open TransferCore TransferSem

/-! Construct the dependent output/volume/encryption/routing tail over one
semantic witness. The registry, users, authorization and spends must already
have been established on the base. This is an explicit partial-construction
interface, not all-row completeness or a Rust witness correspondence theorem. -/

def outputStage (c : Crypto) (base : TransferSem.Witness)
    (i : TransferOutputRecoveryCompletion.LegalOutputInputs c) : TransferSem.Witness :=
  { base with outputs := TransferOutputRecoveryCompletion.constructOutputs c base i }

def volumeStage (c : Crypto) (base : TransferSem.Witness)
    (o : TransferOutputRecoveryCompletion.LegalOutputInputs c)
    (v : TransferVolumeBranchCompletion.LegalVolumeInputs c (outputStage c base o)) :
    TransferSem.Witness :=
  { outputStage c base o with volume :=
      TransferVolumeBranchCompletion.construct c (outputStage c base o) v }

def encryptionStage (c : Crypto) (base : TransferSem.Witness)
    (o : TransferOutputRecoveryCompletion.LegalOutputInputs c)
    (v : TransferVolumeBranchCompletion.LegalVolumeInputs c (outputStage c base o))
    (e : TransferEncryptionBranchCompletion.LegalEncryptionInputs c (volumeStage c base o v)) :
    TransferSem.Witness :=
  { volumeStage c base o v with encryption :=
      TransferEncryptionBranchCompletion.construct c (volumeStage c base o v) e }

structure Inputs (c : Crypto) (base : TransferSem.Witness) where
  output : TransferOutputRecoveryCompletion.LegalOutputInputs c
  volume : TransferVolumeBranchCompletion.LegalVolumeInputs c (outputStage c base output)
  encryption : TransferEncryptionBranchCompletion.LegalEncryptionInputs c
    (volumeStage c base output volume)
  routing : TransferRoutingBranchCompletion.LegalRoutingInputs
  outputBlindingCanonical : ∀ slot, (output.raw slot).blinding < fieldModulus
  outputSeedCanonical : ∀ slot, (output.raw slot).seed < fieldModulus
  outputSaltCanonical : ∀ slot, (output.raw slot).salt < fieldModulus
  priorBlindingCanonical : volume.priorBlinding < fieldModulus
  successorBlindingCanonical : volume.successorBlinding < fieldModulus
  priorSiblingsCanonical : fieldsCanonical (pathFields volume.priorSiblings)
  routingHeightCanonical : routing.height < fieldModulus

def construct (c : Crypto) (base : TransferSem.Witness) (i : Inputs c base) :
    TransferSem.Witness :=
  let beforeRouting := encryptionStage c base i.output i.volume i.encryption
  { beforeRouting with routing := TransferRoutingBranchCompletion.construct c beforeRouting i.routing }

def EarlierComponents (c : Crypto) (w : TransferSem.Witness) : Prop :=
  RegistrySem c w ∧ UserSem c w w.sender ∧ UserSem c w w.receiver ∧
  AuthorizationSem c w ∧ ∀ slot, SpendSem c w slot

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness) (i : Inputs c base) :
    { construct c base i with
      outputs := base.outputs
      volume := base.volume
      encryption := base.encryption
      routing := base.routing } = base := by
  cases base
  rfl

private theorem earlier_components_frame (c : Crypto) (base : TransferSem.Witness)
    (outputs : Fin 2 → Output) (volume : Volume) (encryption : Encryption) (routing : Routing) :
    EarlierComponents c { base with
      outputs := outputs
      volume := volume
      encryption := encryption
      routing := routing } = EarlierComponents c base := rfl

theorem earlier_components_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : Inputs c base) :
    EarlierComponents c (construct c base i) = EarlierComponents c base := by
  have frame := earlier_components_frame c (construct c base i)
    base.outputs base.volume base.encryption base.routing
  rw [restore_full_record] at frame
  exact frame.symm

theorem constructed_tail_components (c : Crypto) (base : TransferSem.Witness)
    (i : Inputs c base) :
    (∀ slot, OutputSem c (construct c base i) slot) ∧
    VolumeSem c (construct c base i) ∧ EncryptionSem c (construct c base i) ∧
    RoutingSem c (construct c base i) := by
  have outputs := TransferOutputRecoveryCompletion.constructed_output_semantics c base i.output
  have volume := TransferVolumeBranchCompletion.constructed_volume_semantics c
    (outputStage c base i.output) i.volume
  have encryption := TransferEncryptionBranchCompletion.constructed_encryption_semantics c
    (volumeStage c base i.output i.volume) i.encryption
  have routing := TransferRoutingBranchCompletion.constructed_routing_semantics c
    (encryptionStage c base i.output i.volume i.encryption) i.routing
  exact ⟨outputs, volume, encryption, routing⟩

theorem constructed_tail_canonical (c : Crypto) (base : TransferSem.Witness)
    (i : Inputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) :
    CanonicalWitness (construct c base i) := by
  have outputs := TransferOutputRecoveryCompletion.canonical_witness_preserved c base i.output
    baseCanonical cryptoCanonical i.outputBlindingCanonical i.outputSeedCanonical i.outputSaltCanonical
  have volume := TransferVolumeBranchCompletion.canonical_witness_preserved c
    (outputStage c base i.output) i.volume outputs cryptoCanonical
    i.priorBlindingCanonical i.successorBlindingCanonical i.priorSiblingsCanonical
  have encryption := TransferEncryptionBranchCompletion.canonical_witness_preserved c
    (volumeStage c base i.output i.volume) i.encryption volume cryptoCanonical
  exact TransferRoutingBranchCompletion.canonical_witness_preserved c
    (encryptionStage c base i.output i.volume i.encryption) i.routing encryption
    cryptoCanonical i.routingHeightCanonical

/-- Output amounts change the balance. Derive the new input bounds from the
raw output legality and retained spends; never transport an old balance value. -/
theorem constructed_balance_inputs (c : Crypto) (base : TransferSem.Witness)
    (i : Inputs c base) (spends : ∀ slot, SpendSem c base slot)
    (blindingBound : base.blinding < scalarOrder)
    (assetGeneratorNonidentity : nonidentity (c.assetGenerator base.asset)) :
    BalanceSem c (construct c base i) := by
  change BalanceInputsSem (base.spends 0).amount (base.spends 1).amount
    (i.output.raw 0).amount (i.output.raw 1).amount base.blinding ∧
    nonidentity (c.assetGenerator base.asset)
  exact ⟨⟨(spends 0).1, (spends 1).1, i.output.amountBounded 0,
    i.output.amountBounded 1, blindingBound⟩, assetGeneratorNonidentity⟩

theorem constructed_components_from_earlier (c : Crypto) (base : TransferSem.Witness)
    (i : Inputs c base) (earlier : EarlierComponents c base)
    (blindingBound : base.blinding < scalarOrder)
    (assetGeneratorNonidentity : nonidentity (c.assetGenerator base.asset)) :
    ComponentsSem c (construct c base i) := by
  have current : EarlierComponents c (construct c base i) := by
    rw [earlier_components_preserved]
    exact earlier
  rcases current with ⟨registry, sender, receiver, authorization, spends⟩
  rcases constructed_tail_components c base i with ⟨outputs, volume, encryption, routing⟩
  exact ⟨registry, sender, receiver, authorization, spends, outputs, volume, routing,
    encryption, constructed_balance_inputs c base i earlier.2.2.2.2 blindingBound
      assetGeneratorNonidentity⟩

/-- Conditional semantic assembly from independently constructed later inputs
and the explicitly open earlier-component interface. No TransferSem or complete
ComponentsSem premise, no row assignment or decoded Rust result is assumed. -/
theorem constructed_transfer_sem_from_earlier (c : Crypto) (base : TransferSem.Witness)
    (i : Inputs c base) (earlier : EarlierComponents c base)
    (baseCanonical : CanonicalWitness base) (cryptoCanonical : CanonicalCrypto c)
    (blindingBound : base.blinding < scalarOrder)
    (assetGeneratorNonidentity : nonidentity (c.assetGenerator base.asset)) :
    TransferSem.TransferSem c (construct c base i) :=
  TransferPublicCanonicality.transfer_sem_of_components c (construct c base i)
    (constructed_tail_canonical c base i baseCanonical cryptoCanonical) cryptoCanonical
    (constructed_components_from_earlier c base i earlier blindingBound assetGeneratorNonidentity)

set_option pp.all true in
#check @earlier_components_preserved
#print axioms earlier_components_preserved
set_option pp.all true in
#check @restore_full_record
#print axioms restore_full_record
set_option pp.all true in
#check @constructed_tail_components
#print axioms constructed_tail_components
set_option pp.all true in
#check @constructed_tail_canonical
#print axioms constructed_tail_canonical
set_option pp.all true in
#check @constructed_balance_inputs
#print axioms constructed_balance_inputs
set_option pp.all true in
#check @constructed_components_from_earlier
#print axioms constructed_components_from_earlier
set_option pp.all true in
#check @constructed_transfer_sem_from_earlier
#print axioms constructed_transfer_sem_from_earlier

end ShielddSecurity.TransferSemanticTailConstruction
