import ShielddSecurity.TransferAcceptance

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferNativeSignaturePolicy

open TransferAcceptance

/-!
Executable policy over a complete retained native carrier B. Ordered effect
preimages, complete body encoding, proof count and aggregate key are separate
functions of that same B. This model checks the exact arguments supplied to
signature verifiers. Their cryptographic security, the native hash/codec/group
views, extraction of every action and fee slot, and Rust refinement remain
explicit separate obligations. Natural zero represents the decoded identity.
-/

structure Carrier (B : Type) where
  body : B
  anchor : Nat
  bindingSignature : List Nat

structure Spend where
  key : Nat
  anchor : Nat
  signature : List Nat

def SpendBound (verify : Nat → Nat → List Nat → Bool)
    (message anchor : Nat) (spend : Spend) : Prop :=
  spend.anchor = anchor ∧ spend.key ≠ 0 ∧
    verify spend.key message spend.signature = true

instance (verify : Nat → Nat → List Nat → Bool)
    (message anchor : Nat) (spend : Spend) :
    Decidable (SpendBound verify message anchor spend) := by
  unfold SpendBound
  infer_instance

instance (count : Nat) (identity sentinel verified : Bool) :
    Decidable (BindingMode count identity sentinel verified) := by
  unfold BindingMode
  infer_instance

def checkSpends (verify : Nat → Nat → List Nat → Bool)
    (message anchor : Nat) : List Spend → Option Unit
  | [] => some ()
  | spend :: rest =>
      if SpendBound verify message anchor spend then checkSpends verify message anchor rest
      else none

def bindingPolicy {B : Type} (encode : B → List Nat) (authHash : List Nat → Nat)
    (proofCount bindingKey : B → Nat) (verify : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B) : Prop :=
  BindingMode (proofCount carrier.body) (decide (bindingKey carrier.body = 0))
    (decide (carrier.bindingSignature = List.replicate 64 0))
    (verify (bindingKey carrier.body) (authHash (encode carrier.body)) carrier.bindingSignature)

instance {B : Type} (encode : B → List Nat) (authHash : List Nat → Nat)
    (proofCount bindingKey : B → Nat) (verify : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B) : Decidable (bindingPolicy encode authHash proofCount bindingKey
      verify carrier) := by
  unfold bindingPolicy
  infer_instance

def runPolicy {B : Type} (encode effectFields : B → List Nat)
    (authHash effectHash : List Nat → Nat) (proofCount bindingKey : B → Nat)
    (spends : B → List Spend) (verifyBinding verifySpend : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B) : Option Unit :=
  if bindingPolicy encode authHash proofCount bindingKey verifyBinding carrier then
    checkSpends verifySpend (effectHash (effectFields carrier.body)) carrier.anchor
      (spends carrier.body)
  else none

theorem spend_checks_success (verify : Nat → Nat → List Nat → Bool)
    (message anchor : Nat) (spends : List Spend)
    (success : checkSpends verify message anchor spends = some ()) :
    ∀ spend ∈ spends, SpendBound verify message anchor spend := by
  induction spends with
  | nil => simp
  | cons first rest ih =>
      by_cases bound : SpendBound verify message anchor first
      · have tail : checkSpends verify message anchor rest = some () := by
          simpa only [checkSpends, if_pos bound] using success
        intro spend inside
        rcases List.mem_cons.mp inside with same | present
        · subst spend
          exact bound
        · exact ih tail spend present
      · simp only [checkSpends, if_neg bound] at success
        cases success

theorem full_carrier_signature_arguments {B : Type} (encode effectFields : B → List Nat)
    (authHash effectHash : List Nat → Nat) (proofCount bindingKey : B → Nat)
    (spends : B → List Spend) (verifyBinding verifySpend : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B)
    (success : runPolicy encode effectFields authHash effectHash proofCount bindingKey
      spends verifyBinding verifySpend carrier = some ()) :
    bindingPolicy encode authHash proofCount bindingKey verifyBinding carrier ∧
      ∀ spend ∈ spends carrier.body,
        SpendBound verifySpend (effectHash (effectFields carrier.body)) carrier.anchor spend := by
  by_cases bound : bindingPolicy encode authHash proofCount bindingKey verifyBinding carrier
  · have checked : checkSpends verifySpend (effectHash (effectFields carrier.body))
        carrier.anchor (spends carrier.body) = some () := by
      simpa only [runPolicy, if_pos bound] using success
    exact ⟨bound, spend_checks_success verifySpend (effectHash (effectFields carrier.body))
      carrier.anchor (spends carrier.body) checked⟩
  · simp only [runPolicy, if_neg bound] at success
    cases success

theorem proof_bearing_exact_binding_message {B : Type} (encode effectFields : B → List Nat)
    (authHash effectHash : List Nat → Nat) (proofCount bindingKey : B → Nat)
    (spends : B → List Spend) (verifyBinding verifySpend : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B) (positive : 0 < proofCount carrier.body)
    (success : runPolicy encode effectFields authHash effectHash proofCount bindingKey
      spends verifyBinding verifySpend carrier = some ()) :
    bindingKey carrier.body ≠ 0 ∧
      verifyBinding (bindingKey carrier.body) (authHash (encode carrier.body))
        carrier.bindingSignature = true := by
  have bound := (full_carrier_signature_arguments encode effectFields authHash effectHash
    proofCount bindingKey spends verifyBinding verifySpend carrier success).1
  have nonidentity := proof_bearing_binding_nonidentity (proofCount carrier.body)
    (decide (bindingKey carrier.body = 0))
    (decide (carrier.bindingSignature = List.replicate 64 0))
    (verifyBinding (bindingKey carrier.body) (authHash (encode carrier.body))
      carrier.bindingSignature) positive bound
  constructor
  · intro zero
    simpa [zero] using nonidentity
  · simpa [bindingPolicy, BindingMode, nonidentity] using bound

theorem wrong_action_anchor_refused {B : Type} (encode effectFields : B → List Nat)
    (authHash effectHash : List Nat → Nat) (proofCount bindingKey : B → Nat)
    (spends : B → List Spend) (verifyBinding verifySpend : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B) (spend : Spend) (inside : spend ∈ spends carrier.body)
    (wrong : spend.anchor ≠ carrier.anchor) :
    runPolicy encode effectFields authHash effectHash proofCount bindingKey
      spends verifyBinding verifySpend carrier ≠ some () := by
  intro success
  exact wrong ((full_carrier_signature_arguments encode effectFields authHash effectHash
    proofCount bindingKey spends verifyBinding verifySpend carrier success).2 spend inside).1

theorem identity_action_key_refused {B : Type} (encode effectFields : B → List Nat)
    (authHash effectHash : List Nat → Nat) (proofCount bindingKey : B → Nat)
    (spends : B → List Spend) (verifyBinding verifySpend : Nat → Nat → List Nat → Bool)
    (carrier : Carrier B) (spend : Spend) (inside : spend ∈ spends carrier.body)
    (identity : spend.key = 0) :
    runPolicy encode effectFields authHash effectHash proofCount bindingKey
      spends verifyBinding verifySpend carrier ≠ some () := by
  intro success
  exact ((full_carrier_signature_arguments encode effectFields authHash effectHash
    proofCount bindingKey spends verifyBinding verifySpend carrier success).2 spend inside).2.1
    identity

set_option pp.all true in
#check @spend_checks_success
#print axioms spend_checks_success
set_option pp.all true in
#check @full_carrier_signature_arguments
#print axioms full_carrier_signature_arguments
set_option pp.all true in
#check @proof_bearing_exact_binding_message
#print axioms proof_bearing_exact_binding_message
set_option pp.all true in
#check @wrong_action_anchor_refused
#print axioms wrong_action_anchor_refused
set_option pp.all true in
#check @identity_action_key_refused
#print axioms identity_action_key_refused

end ShielddSecurity.TransferNativeSignaturePolicy
