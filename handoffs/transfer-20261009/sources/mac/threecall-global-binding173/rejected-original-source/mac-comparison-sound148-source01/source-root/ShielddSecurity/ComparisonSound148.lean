import ShielddSecurity.LexicographicComparison144
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ComparisonSound148
open CompilerArithmeticTransport41
variable {F : Type} [Field F]
theorem zero_flag (delta inverse flag : F) (unit : delta*inverse+flag=1)
    (annihilated : delta*flag=0) : flag=FieldZeroSeed125.flag delta := by
  by_cases zero : delta=0
  · have same : flag=1 := by simpa only [zero,zero_mul,zero_add] using unit
    simpa only [FieldZeroSeed125.flag,if_pos zero] using same
  · have same : flag=0 := (mul_eq_zero.mp annihilated).resolve_left zero
    simpa only [FieldZeroSeed125.flag,if_neg zero] using same
variable [CharP F p]
theorem bounded_solution (width a b difference : Nat) (flag : F)
    (left : a<2^width) (right : b<2^width) (diffBound : difference<2^width)
    (modulusBound : 2^(width+1)<p) (binary : flag=0 ∨ flag=1)
    (balance : (b:F)-(a:F)=(difference:F)-flag*(2^width:F)) :
    flag=BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow a b) ∧
      difference=BoundedLimbComparison119.difference width a b := by
  have positive : 0<2^width := pow_pos (by decide) _
  have two : 2^width+2^width<p := by simpa only [Nat.pow_succ,Nat.mul_two] using modulusBound
  have bBound : b<p := by omega
  have dBound : difference+a<p := by omega
  rcases binary with zero | one
  · have equal : (b:F)=((difference+a:Nat):F) := by
      rw [Nat.cast_add]
      rw [zero,zero_mul,sub_zero] at balance
      linear_combination balance
    have natEqual:=CapturedEpochHints62.cast_small_unique b (difference+a) bBound dBound equal
    have before : a≤b := by omega
    have noBorrow : ¬b<a := by omega
    constructor
    · rw [zero]
      simp only [BoundedLimbComparison119.borrow,decide_eq_false_iff_not.mpr noBorrow,
        BinaryComparison100.bit,Bool.false_eq_true,if_false]
    · simp only [BoundedLimbComparison119.difference,if_pos before]
      omega
  · have equal : ((b+2^width:Nat):F)=((difference+a:Nat):F) := by
      rw [Nat.cast_add,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
      rw [one,one_mul] at balance
      linear_combination balance
    have sumBound : b+2^width<p := by omega
    have natEqual:=CapturedEpochHints62.cast_small_unique (b+2^width) (difference+a) sumBound dBound equal
    have after : b<a := by omega
    have noBefore : ¬a≤b := by omega
    constructor
    · rw [one]
      simp only [BoundedLimbComparison119.borrow,decide_eq_true_eq.mpr after,
        BinaryComparison100.bit,if_true]
    · simp only [BoundedLimbComparison119.difference,if_neg noBefore]
      omega
end ShielddSecurity.ComparisonSound148

set_option pp.all true in
#check @ShielddSecurity.ComparisonSound148.zero_flag
#print axioms ShielddSecurity.ComparisonSound148.zero_flag
set_option pp.all true in
#check @ShielddSecurity.ComparisonSound148.bounded_solution
#print axioms ShielddSecurity.ComparisonSound148.bounded_solution
