import ShielddSecurity.CapturedEpochRange60
import ShielddSecurity.CapturedEpochNonzero61
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedEpochHints62
open CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
noncomputable def seeded (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedEpochNonzero61.seeded (CapturedEpochRange60.completed base n)
theorem seeded_outside (base : Nat → F) (n column : Nat)
    (outside : column<49 ∨ 115≤column) : seeded base n column=base column := by
  have different : column≠113 ∧ column≠114 := by omega
  exact (CapturedEpochNonzero61.seeded_outside _ column different).trans
    (CapturedEpochRange60.completed_outside base n column (by omega))
theorem seeded_fixed (base : Nat → F) (n : Nat) :
    seeded base n 0=base 0 ∧ seeded base n 1=base 1 ∧ seeded base n 2=base 2 ∧
    seeded base n copy=base copy ∧ seeded base n 10=base 10 ∧ seeded base n 34=base 34 :=
  ⟨seeded_outside base n 0 (by decide),seeded_outside base n 1 (by decide),
    seeded_outside base n 2 (by decide),seeded_outside base n copy (by decide),
    seeded_outside base n 10 (by decide),seeded_outside base n 34 (by decide)⟩
theorem seeded_bits (base : Nat → F) (n index : Nat) (bound : index<64) :
    seeded base n (49+index)=CapturedEpochRange60.completed base n (49+index) :=
  CapturedEpochNonzero61.seeded_outside _ _ (by omega)
theorem seeded_range_truth (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) : TruthAt (seeded base n) CapturedEpochRange60.block.recipe 65 := by
  have truth:=(CapturedEpochRange60.truth_iff (CapturedEpochRange60.completed base n)).mp
    (CapturedEpochRange60.completed_truth base n bound meaning)
  apply (CapturedEpochRange60.truth_iff (seeded base n)).mpr
  constructor
  · intro index before
    rw [seeded_bits base n index before]
    exact truth.1 index before
  · have same : CapturedEpochRange60.columns.map (seeded base n)=
        CapturedEpochRange60.columns.map (CapturedEpochRange60.completed base n) := by
      apply List.map_congr_left
      intro column member
      change column∈List.range' 49 64 at member
      obtain ⟨index,before,same⟩:=List.mem_range'.mp member
      simp only [one_mul] at same
      rw [same]
      exact seeded_bits base n index before
    rw [same]
    exact truth.2.trans (CapturedEpochNonzero61.seeded_outside _ 34 (by decide)).symm

theorem seeded_primitive (base : Nat → F) (n : Nat)
    (legalGuard : base 34=0 → base 10=0) : CapturedEpochNonzero61.Primitive (seeded base n) := by
  apply CapturedEpochNonzero61.seeded_primitive
  intro zero
  have epoch:=CapturedEpochRange60.completed_outside base n 34 (by decide)
  have regulated:=CapturedEpochRange60.completed_outside base n 10 (by decide)
  exact regulated.trans (legalGuard (epoch.symm.trans zero))

def HintAgreement (rho sigma : Nat → F) : Prop := ∀ column<115,rho column=sigma column
theorem range_truth_frame (rho sigma : Nat → F) (same : HintAgreement rho sigma)
    (truth : TruthAt rho CapturedEpochRange60.block.recipe 65) :
    TruthAt sigma CapturedEpochRange60.block.recipe 65 := by
  have parts:=(CapturedEpochRange60.truth_iff rho).mp truth
  apply (CapturedEpochRange60.truth_iff sigma).mpr
  constructor
  · intro index before
    rw [←same (49+index) (by omega)]
    exact parts.1 index before
  · have columns : CapturedEpochRange60.columns.map rho=CapturedEpochRange60.columns.map sigma := by
      apply List.map_congr_left
      intro column member
      change column∈List.range' 49 64 at member
      obtain ⟨index,before,equal⟩:=List.mem_range'.mp member
      simp only [one_mul] at equal
      exact same column (by omega)
    exact (congrArg fieldBinary columns).symm.trans (parts.2.trans (same 34 (by decide)))
theorem primitive_frame (rho sigma : Nat → F) (same : HintAgreement rho sigma)
    (truth : CapturedEpochNonzero61.Primitive rho) : CapturedEpochNonzero61.Primitive sigma := by
  unfold CapturedEpochNonzero61.Primitive at truth ⊢
  rw [←same 113 (by decide),←same 34 (by decide),←same 114 (by decide),←same 10 (by decide)]
  exact truth
variable [CharP F p]
theorem seeded_actual_range (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) (linked : base copy=base 0) :
    SatisfiesAt (seeded base n) CapturedEpochRange60.block.actual 65 := by
  apply (satisfies_iff copy 65 CapturedEpochRange60.block (seeded base n) _).mpr
  · exact seeded_range_truth base n bound meaning
  · exact (seeded_outside base n copy (by decide)).trans
      (linked.trans (seeded_outside base n 0 (by decide)).symm)
theorem after_arithmetic_assertions (base rho : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) (legalGuard : base 34=0 → base 10=0)
    (same : HintAgreement (seeded base n) rho) (zero : rho 0=1)
    (linked : rho copy=rho 0)
    (constructedArithmetic : Satisfies rho CapturedEpochNonzero61.arithmetic) :
    SatisfiesAt rho CapturedEpochRange60.block.actual 65 ∧
    SatisfiesAt rho CapturedEpochNonzero61.assertionBlock.actual 4 := by
  constructor
  · exact (satisfies_iff copy 65 CapturedEpochRange60.block rho linked).mpr
      (range_truth_frame _ rho same (seeded_range_truth base n bound meaning))
  · exact CapturedEpochNonzero61.primitive_assertions rho zero linked constructedArithmetic
      (primitive_frame _ rho same (seeded_primitive base n legalGuard))
theorem cast_small_unique (left right : Nat) (leftBound : left<p) (rightBound : right<p)
    (equal : (left : F)=(right : F)) : left=right :=
  by
  by_cases ordered : left≤right
  · by_contra different
    have positive : 0<right-left := by omega
    have zero : ((right-left : Nat) : F)=0 := by
      rw [Nat.cast_sub ordered,←equal,sub_self]
    have divides : p ∣ right-left := (CharP.cast_eq_zero_iff F p _).mp zero
    have lower:=Nat.le_of_dvd positive divides
    omega
  · have reversed : right≤left := by omega
    by_contra different
    have positive : 0<left-right := by omega
    have zero : ((left-right : Nat) : F)=0 := by
      rw [Nat.cast_sub reversed,equal,sub_self]
    have divides : p ∣ left-right := (CharP.cast_eq_zero_iff F p _).mp zero
    have lower:=Nat.le_of_dvd positive divides
    omega
theorem canonical_range_sound (rho : Nat → F) (n : Nat) (canonical : n<p)
    (meaning : (n : F)=rho 34) (truth : TruthAt rho CapturedEpochRange60.block.recipe 65) : n<2^64 := by
  obtain ⟨m,bound,equal⟩:=CapturedEpochRange60.meaning_sound rho truth
  have small : m<p := lt_trans bound (by decide : 2^64<p)
  have same : m=n := cast_small_unique m n small canonical (equal.trans meaning.symm)
  simpa only [same] using bound
theorem actual_canonical_range (rho : Nat → F) (n : Nat) (canonical : n<p)
    (meaning : (n : F)=rho 34) (linked : rho copy=rho 0)
    (satisfied : SatisfiesAt rho CapturedEpochRange60.block.actual 65) : n<2^64 :=
  canonical_range_sound rho n canonical meaning
    ((satisfies_iff copy 65 CapturedEpochRange60.block rho linked).mp satisfied)
theorem actual_regulated_nat (rho : Nat → F) (n : Nat) (meaning : (n : F)=rho 34)
    (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSatisfied : Satisfies rho CapturedEpochNonzero61.arithmetic)
    (assertionsSatisfied : SatisfiesAt rho CapturedEpochNonzero61.assertionBlock.actual 4)
    (regulated : rho 10≠0) : n≠0 := by
  have epoch:=CapturedEpochNonzero61.actual_regulated rho zero linked arithmeticSatisfied assertionsSatisfied regulated
  intro isZero
  apply epoch
  simpa only [isZero,Nat.cast_zero] using meaning.symm
end ShielddSecurity.CapturedEpochHints62

set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded
#print axioms ShielddSecurity.CapturedEpochHints62.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded_outside
#print axioms ShielddSecurity.CapturedEpochHints62.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded_fixed
#print axioms ShielddSecurity.CapturedEpochHints62.seeded_fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded_bits
#print axioms ShielddSecurity.CapturedEpochHints62.seeded_bits
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded_range_truth
#print axioms ShielddSecurity.CapturedEpochHints62.seeded_range_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded_primitive
#print axioms ShielddSecurity.CapturedEpochHints62.seeded_primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.HintAgreement
#print axioms ShielddSecurity.CapturedEpochHints62.HintAgreement
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.range_truth_frame
#print axioms ShielddSecurity.CapturedEpochHints62.range_truth_frame
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.primitive_frame
#print axioms ShielddSecurity.CapturedEpochHints62.primitive_frame
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.seeded_actual_range
#print axioms ShielddSecurity.CapturedEpochHints62.seeded_actual_range
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.after_arithmetic_assertions
#print axioms ShielddSecurity.CapturedEpochHints62.after_arithmetic_assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.cast_small_unique
#print axioms ShielddSecurity.CapturedEpochHints62.cast_small_unique
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.canonical_range_sound
#print axioms ShielddSecurity.CapturedEpochHints62.canonical_range_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.actual_canonical_range
#print axioms ShielddSecurity.CapturedEpochHints62.actual_canonical_range
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochHints62.actual_regulated_nat
#print axioms ShielddSecurity.CapturedEpochHints62.actual_regulated_nat
