import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedEpochHints62
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGlobalEpoch64
open CompilerArithmeticTransport41 CompilerAssertionBlock51

noncomputable def rangeRows : List Row :=
  (List.range 65).filterMap CapturedEpochRange60.block.actual
noncomputable def checkRange : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 177979 65 rangeRows &&
  CompilerRowSlice63.check CapturedEpochRange60.block.actual 0 65 rangeRows
theorem range_checked : checkRange=true := by decide +kernel
noncomputable def checkArithmetic : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 256 6 CapturedEpochNonzero61.arithmetic &&
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 256 6 CapturedEpochNonzero61.arithmetic
theorem arithmetic_checked : checkArithmetic=true := by decide +kernel
noncomputable def checkNonzero : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 178044 4 CapturedEpochNonzero61.assertions &&
  CompilerRowSlice63.check CapturedEpochNonzero61.assertionBlock.actual 0 4 CapturedEpochNonzero61.assertions
theorem nonzero_checked : checkNonzero=true := by decide +kernel

variable {F : Type} [Field F]
theorem full_range_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    SatisfiesAt rho CapturedEpochRange60.block.actual 65 := by
  have checks:=Bool.and_eq_true_iff.mp range_checked
  have rows:=CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt
    200770 177979 65 rangeRows checks.1 (by decide) rho sat
  have localRows:=(CompilerRowSlice63.selected_satisfies_iff
    CapturedEpochRange60.block.actual 0 65 rangeRows checks.2 rho).mp rows
  simpa only [Nat.zero_add] using localRows
theorem full_arithmetic_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho CapturedEpochNonzero61.arithmetic :=
  CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt
    200770 256 6 CapturedEpochNonzero61.arithmetic
    (Bool.and_eq_true_iff.mp arithmetic_checked).1 (by decide) rho sat
theorem full_nonzero_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    SatisfiesAt rho CapturedEpochNonzero61.assertionBlock.actual 4 := by
  have checks:=Bool.and_eq_true_iff.mp nonzero_checked
  have rows:=CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt
    200770 178044 4 CapturedEpochNonzero61.assertions checks.1 (by decide) rho sat
  have localRows:=(CompilerRowSlice63.selected_satisfies_iff
    CapturedEpochNonzero61.assertionBlock.actual 0 4 CapturedEpochNonzero61.assertions checks.2 rho).mp rows
  simpa only [Nat.zero_add] using localRows
variable [CharP F p]
theorem full_range_meaning (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    ∃ n : Nat,n<2^64 ∧ (n : F)=rho 34 :=
  CapturedEpochRange60.actual_sound rho
    (CapturedFullRelation58.verifier_links rho sat).2.2 (full_range_rows rho sat)
theorem full_canonical_bound (rho : Nat → F) (n : Nat) (canonical : n<p)
    (meaning : (n : F)=rho 34)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : n<2^64 :=
  CapturedEpochHints62.actual_canonical_range rho n canonical meaning
    (CapturedFullRelation58.verifier_links rho sat).2.2 (full_range_rows rho sat)
theorem full_primitive (rho : Nat → F) (zero : rho 0=1)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    CapturedEpochNonzero61.Primitive rho :=
  CapturedEpochNonzero61.actual_primitive rho zero
    (CapturedFullRelation58.verifier_links rho sat).2.2
    (full_arithmetic_rows rho sat) (full_nonzero_rows rho sat)
theorem full_regulated_nat (rho : Nat → F) (n : Nat) (meaning : (n : F)=rho 34)
    (zero : rho 0=1) (regulated : rho 10≠0)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : n≠0 :=
  CapturedEpochHints62.actual_regulated_nat rho n meaning zero
    (CapturedFullRelation58.verifier_links rho sat).2.2
    (full_arithmetic_rows rho sat) (full_nonzero_rows rho sat) regulated

noncomputable def prepared (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedEpochHints62.seeded (CompilerVerifierLinks53.seeded base) n
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedFullArithmetic52.completed (prepared base n)
theorem completed_arithmetic (base : Nat → F) (n : Nat) :
    CompilerArithmeticBlock44.SatisfiesAt (completed base n) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedFullArithmetic52.complete (prepared base n)
omit [CharP F p] in
theorem completed_hint_agreement (base : Nat → F) (n : Nat) :
    CapturedEpochHints62.HintAgreement (prepared base n) (completed base n) := by
  intro column bound
  exact (CapturedFullArithmetic52.outside (prepared base n) column (Or.inl (by omega))).symm
omit [CharP F p] in
theorem completed_zero (base : Nat → F) (n : Nat) (zero : base 0=1) : completed base n 0=1 := by
  exact (CapturedFullArithmetic52.fixed (prepared base n)).1.trans
    ((CapturedEpochHints62.seeded_outside _ n 0 (by decide)).trans
      ((CompilerVerifierLinks53.seeded_outside base 0 (by decide)).trans zero))
omit [CharP F p] in
theorem completed_copy (base : Nat → F) (n : Nat) : completed base n copy=completed base n 0 := by
  have fixed:=CapturedFullArithmetic52.fixed (prepared base n)
  calc
    completed base n copy = prepared base n copy := fixed.2.2.2
    _ = CompilerVerifierLinks53.seeded base copy := CapturedEpochHints62.seeded_outside _ n copy (by decide)
    _ = CompilerVerifierLinks53.seeded base 0 := CompilerVerifierLinks53.seeded_copy base
    _ = prepared base n 0 := (CapturedEpochHints62.seeded_outside _ n 0 (by decide)).symm
    _ = completed base n 0 := fixed.1.symm
theorem completed_epoch_assertions (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) (legalGuard : base 34=0 → base 10=0) (zero : base 0=1) :
    SatisfiesAt (completed base n) CapturedEpochRange60.block.actual 65 ∧
    SatisfiesAt (completed base n) CapturedEpochNonzero61.assertionBlock.actual 4 := by
  have epoch:=CompilerVerifierLinks53.seeded_outside base 34 (by decide)
  have regulated:=CompilerVerifierLinks53.seeded_outside base 10 (by decide)
  have localArithmetic:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt
    177954 256 6 CapturedEpochNonzero61.arithmetic
    (Bool.and_eq_true_iff.mp arithmetic_checked).2 (by decide)
    (completed base n) (completed_arithmetic base n)
  exact CapturedEpochHints62.after_arithmetic_assertions
    (CompilerVerifierLinks53.seeded base) (completed base n) n bound (epoch.trans meaning)
    (fun h => regulated.trans (legalGuard (epoch.symm.trans h)))
    (completed_hint_agreement base n) (completed_zero base n zero)
    (completed_copy base n) localArithmetic
omit [CharP F p] in
theorem completed_outside (base : Nat → F) (n column : Nat)
    (arithmeticOutside : column<22738 ∨ 200692≤column)
    (hintOutside : column<49 ∨ 115≤column)
    (verifierOutside : column≠copy ∧ column≠1 ∧ column≠2) : completed base n column=base column :=
  (CapturedFullArithmetic52.outside (prepared base n) column arithmeticOutside).trans
    ((CapturedEpochHints62.seeded_outside _ n column hintOutside).trans
      (CompilerVerifierLinks53.seeded_outside base column verifierOutside))
end ShielddSecurity.CapturedGlobalEpoch64

set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.rangeRows
#print axioms ShielddSecurity.CapturedGlobalEpoch64.rangeRows
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.checkRange
#print axioms ShielddSecurity.CapturedGlobalEpoch64.checkRange
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.range_checked
#print axioms ShielddSecurity.CapturedGlobalEpoch64.range_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.checkArithmetic
#print axioms ShielddSecurity.CapturedGlobalEpoch64.checkArithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.arithmetic_checked
#print axioms ShielddSecurity.CapturedGlobalEpoch64.arithmetic_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.checkNonzero
#print axioms ShielddSecurity.CapturedGlobalEpoch64.checkNonzero
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.nonzero_checked
#print axioms ShielddSecurity.CapturedGlobalEpoch64.nonzero_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_range_rows
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_range_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_arithmetic_rows
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_arithmetic_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_nonzero_rows
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_nonzero_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_range_meaning
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_range_meaning
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_canonical_bound
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_canonical_bound
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_primitive
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.full_regulated_nat
#print axioms ShielddSecurity.CapturedGlobalEpoch64.full_regulated_nat
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.prepared
#print axioms ShielddSecurity.CapturedGlobalEpoch64.prepared
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed_arithmetic
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed_arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed_hint_agreement
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed_hint_agreement
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed_zero
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed_zero
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed_copy
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed_copy
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed_epoch_assertions
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed_epoch_assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedGlobalEpoch64.completed_outside
#print axioms ShielddSecurity.CapturedGlobalEpoch64.completed_outside
