import ShielddSecurity.LowBitMeaning128
import ShielddSecurity.BoundedLimbComparison119
import ShielddSecurity.CompilerArithmeticTransport41
import ShielddSecurity.FieldZeroSeed125
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LexicographicComparison144
open CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem cast_difference_zero_iff (a b : Nat) (ha : a<p) (hb : b<p) :
    (a:F)-(b:F)=0 ↔ a=b := by
  rw [sub_eq_zero]
  constructor
  · exact CharP.natCast_injOn_Iio F p ha hb
  · intro same
    rw [same]
theorem flag_cast_difference (a b : Nat) (ha : a<p) (hb : b<p) :
    FieldZeroSeed125.flag ((a:F)-(b:F))=BinaryComparison100.bit (F:=F) (decide (a=b)) := by
  by_cases same : a=b
  · subst b
    simp [FieldZeroSeed125.flag,BinaryComparison100.bit]
  · have different : (a:F)-(b:F)≠0 := fun h => same ((cast_difference_zero_iff a b ha hb).mp h)
    simp [FieldZeroSeed125.flag,BinaryComparison100.bit,different,same]
theorem lex_le (a b : Nat) (ha : a<2^255) (hb : b<2^255) :
    a≤b ↔ a/2^128<b/2^128 ∨
      (a/2^128=b/2^128 ∧ LowBitMeaning128.low a≤LowBitMeaning128.low b) := by
  have ae:=LowBitMeaning128.recombine a ha
  have be:=LowBitMeaning128.recombine b hb
  have al:=LowBitMeaning128.low_bound a
  have bl:=LowBitMeaning128.low_bound b
  change a=LowBitMeaning128.low a+340282366920938463463374607431768211456*(a/2^128) at ae
  change b=LowBitMeaning128.low b+340282366920938463463374607431768211456*(b/2^128) at be
  change LowBitMeaning128.low a<340282366920938463463374607431768211456 at al
  change LowBitMeaning128.low b<340282366920938463463374607431768211456 at bl
  omega
theorem lex_field (a b : Nat) (ha : a<2^255) (hb : b<2^255) :
    (1-BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow (a/2^128) (b/2^128)))*
      (1-FieldZeroSeed125.flag (((a/2^128:Nat):F)-((b/2^128:Nat):F))*
        BinaryComparison100.bit (F:=F) (BoundedLimbComparison119.borrow (LowBitMeaning128.low a) (LowBitMeaning128.low b)))=
      (if a≤b then (1:F) else 0) := by
  rw [flag_cast_difference _ _
    (Nat.lt_trans (HighBitMeaning122.high_bound a ha) (show 2^127<p by decide))
    (Nat.lt_trans (HighBitMeaning122.high_bound b hb) (show 2^127<p by decide))]
  by_cases same : a/2^128=b/2^128
  · have ord : a≤b ↔ LowBitMeaning128.low a≤LowBitMeaning128.low b := by
      rw [lex_le a b ha hb]
      omega
    by_cases low : LowBitMeaning128.low a≤LowBitMeaning128.low b
    · have whole : a≤b := ord.mpr low
      simp [BoundedLimbComparison119.borrow,BinaryComparison100.bit,same,low,whole,show ¬LowBitMeaning128.low b<LowBitMeaning128.low a by omega]
    · have whole : ¬a≤b := fun h => low (ord.mp h)
      simp [BoundedLimbComparison119.borrow,BinaryComparison100.bit,same,low,whole,show LowBitMeaning128.low b<LowBitMeaning128.low a by omega]
  · by_cases before : a/2^128≤b/2^128
    · have less : a/2^128<b/2^128 := by omega
      have whole : a≤b := (lex_le a b ha hb).mpr (Or.inl less)
      simp [BoundedLimbComparison119.borrow,BinaryComparison100.bit,same,whole,show ¬b/2^128<a/2^128 by omega]
    · have whole : ¬a≤b := by rw [lex_le a b ha hb];omega
      simp [BoundedLimbComparison119.borrow,BinaryComparison100.bit,same,whole,show b/2^128<a/2^128 by omega]
end ShielddSecurity.LexicographicComparison144

set_option pp.all true in
#check @ShielddSecurity.LexicographicComparison144.cast_difference_zero_iff
#print axioms ShielddSecurity.LexicographicComparison144.cast_difference_zero_iff
set_option pp.all true in
#check @ShielddSecurity.LexicographicComparison144.flag_cast_difference
#print axioms ShielddSecurity.LexicographicComparison144.flag_cast_difference
set_option pp.all true in
#check @ShielddSecurity.LexicographicComparison144.lex_le
#print axioms ShielddSecurity.LexicographicComparison144.lex_le
set_option pp.all true in
#check @ShielddSecurity.LexicographicComparison144.lex_field
#print axioms ShielddSecurity.LexicographicComparison144.lex_field
