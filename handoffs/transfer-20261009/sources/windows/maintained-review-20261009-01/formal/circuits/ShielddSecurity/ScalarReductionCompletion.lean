import ShielddSecurity.TransferReduction
import ShielddSecurity.ScalarComparatorCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.ScalarReductionCompletion

/-- Globally functional field decoding supplies actual Euclidean operands.
No quotient/remainder wire value or reduction row truth is a premise. -/
theorem decoded_operands {F : Type} [Field F] (codec : TransferReduction.CanonicalField F) (value : F) :
    codec.decode value / Scalar.order ≤ 8 ∧
      codec.decode value % Scalar.order < Scalar.order ∧
      (codec.decode value / Scalar.order = 8 →
        codec.decode value % Scalar.order ≤ Scalar.lastRemainder) ∧
      ((codec.decode value / Scalar.order : Nat) : F) * (Scalar.order : F) +
        ((codec.decode value % Scalar.order : Nat) : F) = value := by
  let n := codec.decode value
  obtain ⟨q,r,qBound,rBound,last,reduction,meaning⟩ :=
    Scalar.reduction_complete (F := F) n (codec.bounded value)
  have division : n = (n / Scalar.order) * Scalar.order + n % Scalar.order := by
    simpa only [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div n Scalar.order).symm
  have exactReduction : Scalar.Reduction n (n / Scalar.order) (n % Scalar.order) :=
    ⟨division,Nat.mod_lt n (by decide : 0 < Scalar.order)⟩
  have identified := Scalar.reduction_unique reduction exactReduction
  rw [identified.1] at qBound
  rw [identified.2] at rBound
  rw [identified.1,identified.2] at last meaning
  exact ⟨qBound,rBound,last,meaning.trans (codec.roundtrip value)⟩

/-- All four quotient bits are accounted for. With q≤8 the high bit is set
exactly at eight; this establishes the source gate in both branches. -/
theorem quotient_high_iff_eight (bits : List Bool) (width : bits.length = 4)
    (bound : binary bits ≤ 8) : bits.getD 3 false = true ↔ binary bits = 8 := by
  cases bits with
  | nil => simp at width
  | cons b0 tail0 =>
      cases tail0 with
      | nil => simp at width
      | cons b1 tail1 =>
          cases tail1 with
          | nil => simp at width
          | cons b2 tail2 =>
              cases tail2 with
              | nil => simp at width
              | cons b3 tail3 =>
                  cases tail3 with
                  | cons b4 tail4 => simp at width
                  | nil =>
                      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
                        simp [binary,List.getD] at bound ⊢

/-- The terminal product vanishes by the independent Euclidean last cap.
The terminal comparator may be false when q<8; its endpoint is not assumed. -/
theorem terminal_gate {F : Type} [Field F] (q r : Nat)
    (last : q = 8 → r ≤ Scalar.lastRemainder) :
    (if q = 8 then (1 : F) else 0) *
      (1 - (if r ≤ Scalar.lastRemainder then (1 : F) else 0)) = 0 := by
  by_cases high : q = 8
  · simp only [if_pos high,if_pos (last high),sub_self,mul_zero]
  · simp only [if_neg high,zero_mul]

set_option pp.all true in
#check @decoded_operands
#print axioms decoded_operands
set_option pp.all true in
#check @quotient_high_iff_eight
#print axioms quotient_high_iff_eight
set_option pp.all true in
#check @terminal_gate
#print axioms terminal_gate

end ShielddSecurity.ScalarReductionCompletion
