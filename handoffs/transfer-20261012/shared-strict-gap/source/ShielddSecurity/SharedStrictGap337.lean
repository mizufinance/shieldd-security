import ShielddSecurity.HighZeroConstruction334
import ShielddSecurity.CapturedRegistryGap145
import ShielddSecurity.CapturedRegistryGap146
import ShielddSecurity.GapActualRow338
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedStrictGap337
open Compiler CompilerArithmeticTransport41
variable {K : Type} [Field K] [CharP K p]

theorem lexical_product (a b : Nat) (left : a<2^255) (right : b<2^255) :
    (1-BinaryComparison100.bit (F:=K) (BoundedLimbComparison119.borrow (a/2^128) (b/2^128)))*
      (1-FieldZeroSeed125.flag (((a/2^128:Nat):K)-((b/2^128:Nat):K))*
        BinaryComparison100.bit (F:=K) (BoundedLimbComparison119.borrow (a%2^128) (b%2^128))) =
      (if a≤b then 1 else 0) := by
  have result := LexicographicComparison144.lex_field (F:=K) a b left right
  rw [SharedWordLimbMeaning321.canonical_low a left,SharedWordLimbMeaning321.canonical_low b right] at result
  exact result


set_option pp.all true in
#check @ShielddSecurity.SharedStrictGap337.lexical_product
#print axioms ShielddSecurity.SharedStrictGap337.lexical_product

theorem legal_gap_expression (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) :
    ((1-(if w.regulated then (1:K) else 0))*(1-(1-(if w.asset≤w.registry.value then 1 else 0))*
      (1-(if w.registry.nextValue≤w.asset then 1 else 0)))) = 0 := by
  cases flag : w.regulated
  · have branch:=legal.2.2.2.2.2.2.2.2.2.2
    simp only [flag,Bool.false_eq_true,if_false] at branch
    have noFirst : ¬w.asset≤w.registry.value := by omega
    have noSecond : ¬w.registry.nextValue≤w.asset := by omega
    simp only [flag,Bool.false_eq_true,if_false,if_neg noFirst,if_neg noSecond,sub_zero,mul_one,sub_self,mul_zero]
  · simp only [flag,if_true,sub_self,zero_mul]

end ShielddSecurity.SharedStrictGap337
namespace ShielddSecurity.SharedStrictGap337
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open HighZeroCompletionFrame332


set_option pp.all true in
#check @ShielddSecurity.SharedStrictGap337.legal_gap_expression
#print axioms ShielddSecurity.SharedStrictGap337.legal_gap_expression

theorem first_comparison (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    (1-assignment original c w initial 981)*(1-assignment original c w initial 1110*assignment original c w initial 1112) =
      (if w.asset≤w.registry.value then 1 else 0) := by
  have high := ComparisonBorrowFrame324.completed_value (HighZeroSeed329.seed original w) c w initial 981 (by decide)
  have low := ComparisonBorrowFrame324.completed_value (HighZeroSeed329.seed original w) c w initial 1112 (by decide)
  have equal := HighZeroCompletionFrame332.first_flag original c w initial
  change assignment original c w initial 981=ComparisonBorrowFrame324.value w 981 at high
  change assignment original c w initial 1112=ComparisonBorrowFrame324.value w 1112 at low
  rw [high,low,equal]
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  exact lexical_product w.asset w.registry.value canon.1 canon.2.1


set_option pp.all true in
#check @ShielddSecurity.SharedStrictGap337.first_comparison
#print axioms ShielddSecurity.SharedStrictGap337.first_comparison

theorem second_comparison (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    (1-assignment original c w initial 1242)*(1-assignment original c w initial 1371*assignment original c w initial 1373) =
      (if w.registry.nextValue≤w.asset then 1 else 0) := by
  have high := ComparisonBorrowFrame324.completed_value (HighZeroSeed329.seed original w) c w initial 1242 (by decide)
  have low := ComparisonBorrowFrame324.completed_value (HighZeroSeed329.seed original w) c w initial 1373 (by decide)
  have equal := HighZeroCompletionFrame332.second_flag original c w initial
  change assignment original c w initial 1242=ComparisonBorrowFrame324.value w 1242 at high
  change assignment original c w initial 1373=ComparisonBorrowFrame324.value w 1373 at low
  rw [high,low,equal]
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  exact lexical_product w.registry.nextValue w.asset canon.2.2 canon.1


set_option pp.all true in
#check @ShielddSecurity.SharedStrictGap337.second_comparison
#print axioms ShielddSecurity.SharedStrictGap337.second_comparison

theorem gap_zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) : assignment original c w initial 33788=0 := by
  have polynomial := CapturedRegistryGap145.gap_polynomial (assignment original c w initial)
    (SharedHighZeroRows333.arithmetic original c w initial) (SharedHighZeroRows333.zero original c w initial)
    (SharedComparisonBlocks327.linked (HighZeroSeed329.seed original w) c w initial)
  have control := SharedRegulatedValue316.control_meaning
    (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w initial
  change assignment original c w initial 10=(if w.regulated then 1 else 0) at control
  rw [first_comparison original c w initial legal,second_comparison original c w initial legal,control] at polynomial
  exact polynomial.trans (legal_gap_expression (K:=F) (crypto c) w legal.2.1.1)


set_option pp.all true in
#check @ShielddSecurity.SharedStrictGap337.gap_zero
#print axioms ShielddSecurity.SharedStrictGap337.gap_zero

theorem actual_row (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (179421+index)) 1 := by
  exact GapActualRow338.of_value (assignment original c w initial) (gap_zero original c w initial legal)
end ShielddSecurity.SharedStrictGap337

set_option pp.all true in
#check @ShielddSecurity.SharedStrictGap337.actual_row
#print axioms ShielddSecurity.SharedStrictGap337.actual_row
