import ShielddSecurity.CapturedRegistryHighLimb121
import ShielddSecurity.CapturedRegistryLowLimb130
import ShielddSecurity.CapturedNextHighLimb134
import ShielddSecurity.CapturedNextLowLimb141
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ComparisonSeedFixed325
variable {F : Type} [Field F]

theorem write_fixed (base : Nat → F) (start width n : Nat)
    (bits : ∀ index < width, base (start+index)=if (encodeBits width n)[index]?.getD false then 1 else 0) :
    writeBits base start (encodeBits width n)=base := by
  funext column
  by_cases inside : start ≤ column ∧ column < start+width
  · have bound : column-start < width := by omega
    have index : start+(column-start)=column := by omega
    have known := bits (column-start) bound
    rw [index] at known
    unfold writeBits
    rw [encodeBits_length,if_pos inside]
    exact known.symm
  · exact writeBits_preserves base start (encodeBits width n) column (by rw [encodeBits_length]; omega)

theorem first_high (base : Nat → F) (a b : Nat)
    (borrow : base 981=BinaryComparison100.bit (BoundedLimbComparison119.borrow a b))
    (difference : base 982=(BoundedLimbComparison119.difference 127 a b:F))
    (bits : ∀ index < 127, base (983+index)=
      if (encodeBits 127 (BoundedLimbComparison119.difference 127 a b))[index]?.getD false then 1 else 0) :
    CapturedRegistryHighLimb121.seeded base a b=base := by
  have prepared : CapturedRegistryHighLimb121.prepared base a b=base := by
    funext column
    unfold CapturedRegistryHighLimb121.prepared
    split_ifs with flag value
    · subst column; exact borrow.symm
    · subst column; exact difference.symm
    · rfl
  unfold CapturedRegistryHighLimb121.seeded
  rw [prepared]
  exact write_fixed base 983 127 _ bits

theorem first_low (base : Nat → F) (a b : Nat)
    (borrow : base 1112=BinaryComparison100.bit (BoundedLimbComparison119.borrow a b))
    (difference : base 1113=(BoundedLimbComparison119.difference 128 a b:F))
    (bits : ∀ index < 128, base (1114+index)=
      if (encodeBits 128 (BoundedLimbComparison119.difference 128 a b))[index]?.getD false then 1 else 0) :
    CapturedRegistryLowLimb130.seeded base a b=base := by
  have prepared : CapturedRegistryLowLimb130.prepared base a b=base := by
    funext column
    unfold CapturedRegistryLowLimb130.prepared
    split_ifs with flag value
    · subst column; exact borrow.symm
    · subst column; exact difference.symm
    · rfl
  unfold CapturedRegistryLowLimb130.seeded
  rw [prepared]
  exact write_fixed base 1114 128 _ bits

theorem second_high (base : Nat → F) (a b : Nat)
    (borrow : base 1242=BinaryComparison100.bit (BoundedLimbComparison119.borrow a b))
    (difference : base 1243=(BoundedLimbComparison119.difference 127 a b:F))
    (bits : ∀ index < 127, base (1244+index)=
      if (encodeBits 127 (BoundedLimbComparison119.difference 127 a b))[index]?.getD false then 1 else 0) :
    CapturedNextHighLimb134.seeded base a b=base := by
  have prepared : CapturedNextHighLimb134.prepared base a b=base := by
    funext column
    unfold CapturedNextHighLimb134.prepared
    split_ifs with flag value
    · subst column; exact borrow.symm
    · subst column; exact difference.symm
    · rfl
  unfold CapturedNextHighLimb134.seeded
  rw [prepared]
  exact write_fixed base 1244 127 _ bits

theorem second_low (base : Nat → F) (a b : Nat)
    (borrow : base 1373=BinaryComparison100.bit (BoundedLimbComparison119.borrow a b))
    (difference : base 1374=(BoundedLimbComparison119.difference 128 a b:F))
    (bits : ∀ index < 128, base (1375+index)=
      if (encodeBits 128 (BoundedLimbComparison119.difference 128 a b))[index]?.getD false then 1 else 0) :
    CapturedNextLowLimb141.seeded base a b=base := by
  have prepared : CapturedNextLowLimb141.prepared base a b=base := by
    funext column
    unfold CapturedNextLowLimb141.prepared
    split_ifs with flag value
    · subst column; exact borrow.symm
    · subst column; exact difference.symm
    · rfl
  unfold CapturedNextLowLimb141.seeded
  rw [prepared]
  exact write_fixed base 1375 128 _ bits

end ShielddSecurity.ComparisonSeedFixed325

set_option pp.all true in
#check @ShielddSecurity.ComparisonSeedFixed325.write_fixed
#print axioms ShielddSecurity.ComparisonSeedFixed325.write_fixed

set_option pp.all true in
#check @ShielddSecurity.ComparisonSeedFixed325.first_high
#print axioms ShielddSecurity.ComparisonSeedFixed325.first_high

set_option pp.all true in
#check @ShielddSecurity.ComparisonSeedFixed325.first_low
#print axioms ShielddSecurity.ComparisonSeedFixed325.first_low

set_option pp.all true in
#check @ShielddSecurity.ComparisonSeedFixed325.second_high
#print axioms ShielddSecurity.ComparisonSeedFixed325.second_high

set_option pp.all true in
#check @ShielddSecurity.ComparisonSeedFixed325.second_low
#print axioms ShielddSecurity.ComparisonSeedFixed325.second_low
