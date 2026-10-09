import ShielddSecurity.Scalar

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.RoutingBitSemantics

variable {F : Type} [Field F]

def bit (value : Bool) : F := if value then 1 else 0

def select (flag left right : F) : F := right + flag * (left - right)

/-- The source selection arithmetic computes the same Boolean branch. -/
theorem select_bit (flag left right : Bool) :
    select (bit flag : F) (bit left) (bit right) =
      bit (if flag then left else right) := by
  cases flag <;> cases left <;> cases right <;> simp [select, bit]

/-- The compiler's field expression for BoolVar OR has the source truth table. -/
theorem or_bit (left right : Bool) :
    (bit left : F) + bit right - bit left * bit right = bit (left || right) := by
  cases left <;> cases right <;> simp [bit]

/-- Exactly the 32 ordering assertions force the two legal precisions to be
ordered. No promised precision-order conclusion is used as a premise. -/
theorem precision_order_sound (regulated unregulated : Nat)
    (regulatedBound : regulated ≤ 32) (unregulatedBound : unregulated ≤ 32)
    (products : ∀ index : Nat, index < 32 →
      (bit (decide (index < regulated)) : F) *
        (1 - bit (decide (index < unregulated))) = 0) :
    regulated ≤ unregulated := by
  by_contra absent
  have reversed : unregulated < regulated := Nat.lt_of_not_ge absent
  have inside : unregulated < 32 := reversed.trans_le regulatedBound
  have impossible := products unregulated inside
  have unequal : (1 : F) ≠ 0 := one_ne_zero
  apply unequal
  simpa [bit, reversed] using impossible

/-- Legal independently supplied precisions construct every ordering product. -/
theorem precision_order_complete (regulated unregulated index : Nat)
    (ordered : regulated ≤ unregulated) :
    (bit (decide (index < regulated)) : F) *
      (1 - bit (decide (index < unregulated))) = 0 := by
  by_cases active : index < regulated
  · have also : index < unregulated := active.trans_le ordered
    simp [bit, active, also]
  · simp [bit, active]

/-- A regulated select uses exactly the appropriate precision threshold. -/
theorem active_bit (regulated : Bool) (first second index : Nat) :
    select (bit regulated : F) (bit (decide (index < first)))
      (bit (decide (index < second))) =
      bit (decide (index < if regulated then first else second)) := by
  cases regulated <;> simp [select, bit]

/-- The nested source selects determine the public bit; its truth does not
come from an assumed matching native tag or an assumed public-bit value. -/
theorem tag_bit (active meaningful route random : Bool) :
    select (bit meaningful : F)
      (select (bit active) (bit route) (bit random)) (bit random) =
      bit (if meaningful && active then route else random) := by
  cases active <;> cases meaningful <;> cases route <;> cases random <;>
    simp [select, bit]

set_option pp.all true in
#check @select_bit
#print axioms select_bit
set_option pp.all true in
#check @or_bit
#print axioms or_bit
set_option pp.all true in
#check @precision_order_sound
#print axioms precision_order_sound
set_option pp.all true in
#check @precision_order_complete
#print axioms precision_order_complete
set_option pp.all true in
#check @active_bit
#print axioms active_bit
set_option pp.all true in
#check @tag_bit
#print axioms tag_bit

end ShielddSecurity.RoutingBitSemantics
