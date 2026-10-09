import ShielddSecurity.ReceiverLifecycle

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.ReceiverLifecycleProductCompletion

variable {F : Type} [Field F]

def materializedRows (left right : Linear) (output auxiliary : Nat) : List Row :=
  ScalarCompletion.productRows left right [] output auxiliary ++
    [⟨[(output,1)],[]⟩,⟨[(output,-1)],[]⟩]

/-- The unit-pivot product is assigned its derived value zero. Either sign of
the actual following equality row is covered; no zero output is passed in. -/
theorem materialized_zero (base : Nat → F) (left right : Linear) (output auxiliary : Nat)
    (distinct : output ≠ auxiliary)
    (fresh : ∀ term ∈ left ++ right, term.1 ∉ [output,auxiliary])
    (zeroProduct : eval base left * eval base right = 0) :
    Satisfies (ScalarCompletion.extendProduct base left right [] output auxiliary)
      (materializedRows left right output auxiliary) ∧
      ScalarCompletion.extendProduct base left right [] output auxiliary output = 0 := by
  have productRows := ScalarCompletion.extend_product_complete base left right [] output auxiliary
    distinct (by simpa only [List.append_nil] using fresh)
  have outputValue : ScalarCompletion.extendProduct base left right [] output auxiliary output = 0 := by
    simp [ScalarCompletion.extendProduct,patchAssignment,ScalarCompletion.productValues,
      zeroProduct,eval]
  refine ⟨?_,outputValue⟩
  intro row member
  rcases List.mem_append.mp member with product | assertion
  · exact productRows row product
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at assertion
    rcases assertion with rfl | rfl
    · simp only [Square,eval,outputValue,Int.cast_one,one_mul,add_zero,zero_mul]
    · simp only [Square,eval,outputValue,Int.cast_neg,Int.cast_one,mul_zero,add_zero,zero_mul]

theorem materialized_preserves (base : Nat → F) (left right : Linear) (output auxiliary column : Nat)
    (outside : column ∉ [output,auxiliary]) :
    ScalarCompletion.extendProduct base left right [] output auxiliary column = base column :=
  ScalarCompletion.extend_product_preserves base left right [] output auxiliary column outside

/-- The actual status predicate gives the zero-product premise via the already
defined encoded lifecycle semantics. This helper supplies only materialized
rows; exact LC/source/row containment and list freshness remain finite actual
instance obligations. -/
theorem enabled_materialized (base : Nat → F) (left right : Linear)
    (output auxiliary : Nat) (distinct : output ≠ auxiliary)
    (fresh : ∀ term ∈ left ++ right, term.1 ∉ [output,auxiliary])
    (n : Nat) (flag : Bool) (index : Nat) (gate : ReceiverLifecycle.GateIndex index)
    (leftValue : eval base left = if flag then 1 else 0)
    (rightValue : eval base right =
      (if (encodeBits 131 n)[index]?.getD false then 1 else 0) - (if index=0 then 1 else 0))
    (guard : flag=true → ReceiverLifecycle.LegalActive n) :
    Satisfies (ScalarCompletion.extendProduct base left right [] output auxiliary)
      (materializedRows left right output auxiliary) ∧
      ScalarCompletion.extendProduct base left right [] output auxiliary output = 0 := by
  apply materialized_zero base left right output auxiliary distinct fresh
  rw [leftValue,rightValue]
  exact ReceiverLifecycle.enabled_product n index flag gate guard

set_option pp.all true in
#check @materialized_zero
#print axioms materialized_zero
set_option pp.all true in
#check @materialized_preserves
#print axioms materialized_preserves
set_option pp.all true in
#check @enabled_materialized
#print axioms enabled_materialized

end ShielddSecurity.ReceiverLifecycleProductCompletion
