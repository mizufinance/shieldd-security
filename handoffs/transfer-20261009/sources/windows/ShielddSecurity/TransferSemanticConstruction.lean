import ShielddSecurity.TransferInitialWitnessConstruction
import ShielddSecurity.TransferRegistryUserCompletion
import ShielddSecurity.TransferAuthorizationBranchCompletion
import ShielddSecurity.TransferSpendBranchCompletion
import ShielddSecurity.TransferSemanticTailConstruction

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-! Ordered construction from raw semantic inputs. Authenticated tree paths,
computed point legality and global crypto/group interpretation are explicit.
Every semantic component is derived on one record; no EarlierComponents,
ComponentsSem or TransferSem fact is supplied. Pinned circuit assignment and
Rust construction correspondence remain separate obligations. -/
namespace ShielddSecurity.TransferSemanticConstruction

open TransferCore TransferSem

def registryStage (c : Crypto) (initial : TransferInitialWitnessConstruction.Inputs)
    (registry : TransferRegistryUserCompletion.RegistryInputs c
      (TransferInitialWitnessConstruction.construct initial)) : TransferSem.Witness :=
  TransferRegistryUserCompletion.constructRegistry c
    (TransferInitialWitnessConstruction.construct initial) registry

def authorizationStage (c : Crypto) (initial : TransferInitialWitnessConstruction.Inputs)
    (registry : TransferRegistryUserCompletion.RegistryInputs c
      (TransferInitialWitnessConstruction.construct initial))
    (authorization : TransferAuthorizationBranchCompletion.RawInputs) : TransferSem.Witness :=
  TransferAuthorizationBranchCompletion.construct c (registryStage c initial registry) authorization

def spendStage (c : Crypto) (initial : TransferInitialWitnessConstruction.Inputs)
    (registry : TransferRegistryUserCompletion.RegistryInputs c
      (TransferInitialWitnessConstruction.construct initial))
    (authorization : TransferAuthorizationBranchCompletion.RawInputs)
    (spends : TransferSpendBranchCompletion.LegalInputs c
      (authorizationStage c initial registry authorization)) : TransferSem.Witness :=
  TransferSpendBranchCompletion.construct c (authorizationStage c initial registry authorization) spends

def userStage (c : Crypto) (initial : TransferInitialWitnessConstruction.Inputs)
    (registry : TransferRegistryUserCompletion.RegistryInputs c
      (TransferInitialWitnessConstruction.construct initial))
    (authorization : TransferAuthorizationBranchCompletion.RawInputs)
    (spends : TransferSpendBranchCompletion.LegalInputs c
      (authorizationStage c initial registry authorization))
    (sender receiver : TransferRegistryUserCompletion.UserPathInputs) : TransferSem.Witness :=
  TransferRegistryUserCompletion.constructUsers (spendStage c initial registry authorization spends) sender receiver

structure Inputs (c : Crypto) where
  initial : TransferInitialWitnessConstruction.Inputs
  initialLegal : TransferInitialWitnessConstruction.Legal initial
  registry : TransferRegistryUserCompletion.RegistryInputs c
    (TransferInitialWitnessConstruction.construct initial)
  authorization : TransferAuthorizationBranchCompletion.RawInputs
  authorizationLegal : TransferAuthorizationBranchCompletion.LegalInputs c
    (registryStage c initial registry) authorization
  spends : TransferSpendBranchCompletion.LegalInputs c
    (authorizationStage c initial registry authorization)
  sender : TransferRegistryUserCompletion.UserPathInputs
  receiver : TransferRegistryUserCompletion.UserPathInputs
  senderLegal : TransferRegistryUserCompletion.LegalUserPath c
    (spendStage c initial registry authorization spends)
    (spendStage c initial registry authorization spends).sender sender
  receiverLegal : TransferRegistryUserCompletion.LegalUserPath c
    (spendStage c initial registry authorization spends)
    (spendStage c initial registry authorization spends).receiver receiver
  tail : TransferSemanticTailConstruction.Inputs c
    (userStage c initial registry authorization spends sender receiver)
  assetGeneratorNonidentity : nonidentity (c.assetGenerator (registryStage c initial registry).asset)

def earlier (c : Crypto) (i : Inputs c) : TransferSem.Witness :=
  userStage c i.initial i.registry i.authorization i.spends i.sender i.receiver

def construct (c : Crypto) (i : Inputs c) : TransferSem.Witness :=
  TransferSemanticTailConstruction.construct c (earlier c i) i.tail

theorem earlier_components_derived (c : Crypto) (i : Inputs c)
    (cryptoCanonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    TransferSemanticTailConstruction.EarlierComponents c (earlier c i) := by
  have registry := TransferRegistryUserCompletion.constructed_registry_semantics c
    (TransferInitialWitnessConstruction.construct i.initial) i.registry
  have authorization := TransferAuthorizationBranchCompletion.constructed_authorization_semantics c
    (registryStage c i.initial i.registry) i.authorization i.authorizationLegal cryptoCanonical group
  have spends := TransferSpendBranchCompletion.constructed_spend_semantics c
    (authorizationStage c i.initial i.registry i.authorization) i.spends
  have users := TransferRegistryUserCompletion.constructed_both_users c
    (spendStage c i.initial i.registry i.authorization i.spends) i.sender i.receiver
    i.senderLegal i.receiverLegal
  exact ⟨registry, users.1, users.2, authorization, spends⟩

theorem earlier_canonical_derived (c : Crypto) (i : Inputs c) (cryptoCanonical : CanonicalCrypto c) :
    CanonicalWitness (earlier c i) := by
  have seed := TransferInitialWitnessConstruction.constructed_canonical i.initial i.initialLegal
  have registry := TransferRegistryUserCompletion.registry_canonical_preserved c
    (TransferInitialWitnessConstruction.construct i.initial) i.registry seed
  have authorization := TransferAuthorizationBranchCompletion.canonical_witness_preserved c
    (registryStage c i.initial i.registry) i.authorization i.authorizationLegal registry cryptoCanonical
  have spends := TransferSpendBranchCompletion.canonical_witness_preserved c
    (authorizationStage c i.initial i.registry i.authorization) i.spends authorization cryptoCanonical
  exact TransferRegistryUserCompletion.users_canonical_preserved c
    (spendStage c i.initial i.registry i.authorization i.spends) i.sender i.receiver
    i.senderLegal i.receiverLegal spends

theorem constructed_transfer_semantics (c : Crypto) (i : Inputs c)
    (cryptoCanonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    TransferSem.TransferSem c (construct c i) :=
  TransferSemanticTailConstruction.constructed_transfer_sem_from_earlier c (earlier c i) i.tail
    (earlier_components_derived c i cryptoCanonical group) (earlier_canonical_derived c i cryptoCanonical)
    cryptoCanonical i.initialLegal.blindingBounded i.assetGeneratorNonidentity

theorem raw_headers_and_selector_preserved (c : Crypto) (i : Inputs c) :
    (construct c i).anchor = i.initial.anchor ∧
    (construct c i).assetAnchor = i.initial.assetAnchor ∧
    (construct c i).userAnchor = i.initial.userAnchor ∧
    (construct c i).timestamp = i.initial.timestamp ∧
    (construct c i).nonce = i.initial.nonce ∧
    (construct c i).blinding = i.initial.blinding ∧
    (construct c i).paddingSeed = i.initial.paddingSeed ∧
    (construct c i).optionalDummy = i.initial.optionalDummy :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem semantic_witness_exists (c : Crypto) (i : Inputs c)
    (cryptoCanonical : CanonicalCrypto c) (group : TransferAuthorizationBranchCompletion.GroupClosure c) :
    ∃ w : TransferSem.Witness, TransferSem.TransferSem c w ∧ w.blinding = i.initial.blinding :=
  ⟨construct c i, constructed_transfer_semantics c i cryptoCanonical group, rfl⟩

set_option pp.all true in
#check @earlier_components_derived
#print axioms earlier_components_derived
set_option pp.all true in
#check @earlier_canonical_derived
#print axioms earlier_canonical_derived
set_option pp.all true in
#check @constructed_transfer_semantics
#print axioms constructed_transfer_semantics
set_option pp.all true in
#check @raw_headers_and_selector_preserved
#print axioms raw_headers_and_selector_preserved
set_option pp.all true in
#check @semantic_witness_exists
#print axioms semantic_witness_exists

end ShielddSecurity.TransferSemanticConstruction
