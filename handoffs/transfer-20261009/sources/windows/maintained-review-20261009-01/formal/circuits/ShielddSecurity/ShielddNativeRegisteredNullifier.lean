import ShielddSecurity.TransferNativeRegulatedSource
import ShielddSecurity.Arithmetic

set_option maxHeartbeats 150000

namespace ShielddSecurity.ShielddNativeRegisteredNullifier

/-! The owned ActionWitness::nullifier_key final control flow, pinned
action_context.rs243–268. The caller's full policy/address/asset/DH objects are
captured by a globally defined `derive` function, independently of the returned
key. Its exact source implementation and the registered-leaf/compiled LC
association remain separate obligations. Successful unregulated execution
does not execute the regulated derivation or establish address legality. -/

def nullifierKey {Policy Q : Type} [DecidableEq Q]
    (walletNk : Q) (regulated : Bool) (policy : Option Policy)
    (derive : Policy → Option Q) (commitment : Q → Q) (registered : Q) : Option Q :=
  if regulated then
    match policy with
    | none => none
    | some chosen => match derive chosen with
      | none => none
      | some key => if commitment key = registered then some key else none
  else some walletNk

theorem unregulated_value {Policy Q : Type} [DecidableEq Q]
    (walletNk : Q) (policy : Option Policy) (derive : Policy → Option Q)
    (commitment : Q → Q) (registered : Q) :
    nullifierKey walletNk false policy derive commitment registered = some walletNk := by
  simp only [nullifierKey,Bool.false_eq_true,ite_false]

theorem regulated_value {Policy Q : Type} [DecidableEq Q]
    (walletNk : Q) (policy : Option Policy) (derive : Policy → Option Q)
    (commitment : Q → Q) (registered key : Q)
    (accepted : nullifierKey walletNk true policy derive commitment registered = some key) :
    ∃ chosen, policy = some chosen ∧ derive chosen = some key ∧ commitment key = registered := by
  cases present : policy with
  | none =>
      simp only [nullifierKey,ite_true,present] at accepted
      cases accepted
  | some chosen =>
      cases derived : derive chosen with
      | none =>
          simp only [nullifierKey,ite_true,present,derived] at accepted
          cases accepted
      | some computed =>
          by_cases matching : commitment computed = registered
          · have same : computed = key := Option.some.inj (by
              simpa only [nullifierKey,ite_true,present,derived,matching] using accepted)
            subst computed
            exact ⟨chosen,rfl,derived,matching⟩
          · simp only [nullifierKey,ite_true,present,derived,matching,ite_false] at accepted
            cases accepted

theorem successful_branches {Policy Q : Type} [DecidableEq Q]
    (walletNk : Q) (regulated : Bool) (policy : Option Policy)
    (derive : Policy → Option Q) (commitment : Q → Q) (registered key : Q)
    (accepted : nullifierKey walletNk regulated policy derive commitment registered = some key) :
    (regulated = false ∧ key = walletNk) ∨
      (regulated = true ∧ ∃ chosen, policy = some chosen ∧
        derive chosen = some key ∧ commitment key = registered) := by
  cases regulated with
  | false =>
      have same : walletNk = key := Option.some.inj (by
        simpa only [unregulated_value] using accepted)
      exact Or.inl ⟨rfl,same.symm⟩
  | true =>
      exact Or.inr ⟨rfl,regulated_value walletNk policy derive commitment registered key accepted⟩

theorem registered_gate {Policy Q F : Type} [DecidableEq Q] [Field F]
    (walletNk : Q) (regulated : Bool) (policy : Option Policy)
    (derive : Policy → Option Q) (commitment : Q → Q) (registered key : Q)
    (fieldValue : Q → F)
    (accepted : nullifierKey walletNk regulated policy derive commitment registered = some key) :
    (if regulated then (1 : F) else 0) *
      (fieldValue (commitment key) - fieldValue registered) = 0 := by
  rcases successful_branches walletNk regulated policy derive commitment registered key accepted with
    ⟨unregulated,_⟩ | ⟨regulated,chosen,present,derived,matching⟩
  · rw [unregulated]
    simp only [Bool.false_eq_true,ite_false,zero_mul]
  · rw [regulated,matching]
    simp only [ite_true,sub_self,mul_zero]

set_option pp.all true in
#check @unregulated_value
#print axioms unregulated_value
set_option pp.all true in
#check @regulated_value
#print axioms regulated_value
set_option pp.all true in
#check @successful_branches
#print axioms successful_branches
set_option pp.all true in
#check @registered_gate
#print axioms registered_gate

end ShielddSecurity.ShielddNativeRegisteredNullifier
