import ShielddSecurity.CapturedGlobalZeroCompletion68
import ShielddSecurity.CapturedRegisteredHints72
import ShielddSecurity.CapturedRegisteredAssertions73
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGlobalRegistered74
open CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def checkArithmetic : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 262 60 CapturedRegisteredAudit70.arithmetic &&
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 262 60 CapturedRegisteredAudit70.arithmetic
theorem arithmetic_checked : checkArithmetic=true := by decide +kernel
noncomputable def checkAssertions : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 178048 35 CapturedRegisteredAudit70.assertions &&
  CompilerRowSlice63.check CapturedRegisteredAudit70.block.actual 0 35 CapturedRegisteredAudit70.assertions
theorem assertions_checked : checkAssertions=true := by decide +kernel
variable {F : Type} [Field F]
theorem full_arithmetic_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho CapturedRegisteredAudit70.arithmetic :=
  CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt 200770 262 60
    CapturedRegisteredAudit70.arithmetic (Bool.and_eq_true_iff.mp arithmetic_checked).1 (by decide) rho sat
theorem full_assertion_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35 := by
  have checks:=Bool.and_eq_true_iff.mp assertions_checked
  have rows:=CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt 200770 178048 35
    CapturedRegisteredAudit70.assertions checks.1 (by decide) rho sat
  have localRows:=(CompilerRowSlice63.selected_satisfies_iff CapturedRegisteredAudit70.block.actual 0 35
    CapturedRegisteredAudit70.assertions checks.2 rho).mp rows
  simpa only [Nat.zero_add] using localRows
theorem selected_global104 (rho : Nat → F)
    (rangeSat : SatisfiesAt rho CapturedEpochRange60.block.actual 65)
    (nonzeroSat : SatisfiesAt rho CapturedEpochNonzero61.assertionBlock.actual 4)
    (zeroSat : SatisfiesAt rho CapturedRegisteredAudit70.block.actual 35) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177979+index)) 104 := by
  have rc:=Bool.and_eq_true_iff.mp CapturedGlobalEpoch64.range_checked
  have nc:=Bool.and_eq_true_iff.mp CapturedGlobalEpoch64.nonzero_checked
  have zc:=Bool.and_eq_true_iff.mp assertions_checked
  have rlist:=(CompilerRowSlice63.selected_satisfies_iff CapturedEpochRange60.block.actual 0 65
    CapturedGlobalEpoch64.rangeRows rc.2 rho).mpr (by simpa only [Nat.zero_add] using rangeSat)
  have nlist:=(CompilerRowSlice63.selected_satisfies_iff CapturedEpochNonzero61.assertionBlock.actual 0 4
    CapturedEpochNonzero61.assertions nc.2 rho).mpr (by simpa only [Nat.zero_add] using nonzeroSat)
  have zlist:=(CompilerRowSlice63.selected_satisfies_iff CapturedRegisteredAudit70.block.actual 0 35
    CapturedRegisteredAudit70.assertions zc.2 rho).mpr (by simpa only [Nat.zero_add] using zeroSat)
  have r:=(CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 177979 65
    CapturedGlobalEpoch64.rangeRows rc.1 rho).mp rlist
  have n:=(CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 178044 4
    CapturedEpochNonzero61.assertions nc.1 rho).mp nlist
  have z:=(CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 178048 35
    CapturedRegisteredAudit70.assertions zc.1 rho).mp zlist
  intro index bound row found
  change CapturedFullRelation58.rowAt (177979+index)=some row at found
  by_cases first : index<65
  · exact r index first row found
  · by_cases second : index<69
    · have equal : 177979+index=178044+(index-65) := by omega
      rw [equal] at found
      exact n (index-65) (by omega) row found
    · have equal : 177979+index=178048+(index-69) := by omega
      rw [equal] at found
      exact z (index-69) (by omega) row found
noncomputable def prepared (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedRegisteredHints72.seeded (CapturedGlobalEpoch64.prepared base n)
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedFullArithmetic52.completed (prepared base n)
theorem prepared_zero (base : Nat → F) (n : Nat) : prepared base n 0=base 0 :=
  (CapturedRegisteredHints72.seeded_outside _ 0 (by omega)).trans
    ((CapturedEpochHints62.seeded_outside _ n 0 (by decide)).trans
      (CompilerVerifierLinks53.seeded_outside base 0 (by decide)))
theorem prepared_copy (base : Nat → F) (n : Nat) : prepared base n copy=prepared base n 0 := by
  calc
    prepared base n copy = CapturedGlobalEpoch64.prepared base n copy := CapturedRegisteredHints72.seeded_outside _ copy (by decide)
    _ = CompilerVerifierLinks53.seeded base copy := CapturedEpochHints62.seeded_outside _ n copy (by decide)
    _ = CompilerVerifierLinks53.seeded base 0 := CompilerVerifierLinks53.seeded_copy base
    _ = CapturedGlobalEpoch64.prepared base n 0 := (CapturedEpochHints62.seeded_outside _ n 0 (by decide)).symm
    _ = prepared base n 0 := (CapturedRegisteredHints72.seeded_outside _ 0 (by omega)).symm
theorem completed_zero (base : Nat → F) (n : Nat) (zero : base 0=1) : completed base n 0=1 :=
  (CapturedFullArithmetic52.fixed (prepared base n)).1.trans ((prepared_zero base n).trans zero)
theorem completed_copy (base : Nat → F) (n : Nat) : completed base n copy=completed base n 0 :=
  ((CapturedFullArithmetic52.fixed (prepared base n)).2.2.2.trans (prepared_copy base n)).trans
    (CapturedFullArithmetic52.fixed (prepared base n)).1.symm
theorem completed_hint_agreement (base : Nat → F) (n : Nat) :
    CapturedEpochHints62.HintAgreement (CapturedGlobalEpoch64.prepared base n) (completed base n) := by
  intro column bound
  exact (CapturedRegisteredHints72.seeded_outside _ column (by omega)).symm.trans
    (CapturedFullArithmetic52.outside (prepared base n) column (Or.inl (by omega))).symm
theorem completed_registered_agreement (base : Nat → F) (n : Nat) :
    ∀ column<135,prepared base n column=completed base n column := fun column bound =>
  (CapturedFullArithmetic52.outside (prepared base n) column (Or.inl (by omega))).symm
theorem completed_primitive (base : Nat → F) (n : Nat) : CapturedRegisteredAudit70.Primitive (completed base n) :=
  CapturedRegisteredHints72.primitive_frame _ _ (completed_registered_agreement base n)
    (CapturedRegisteredHints72.seeded_primitive (CapturedGlobalEpoch64.prepared base n))
theorem completed_guards (base : Nat → F) (n : Nat)
    (legal : CapturedRegisteredHints72.LegalGuards (CapturedGlobalEpoch64.prepared base n)) :
    CapturedRegisteredAudit71.Guards (completed base n) :=
  CapturedRegisteredHints72.guards_frame _ _ (completed_registered_agreement base n)
    (CapturedRegisteredHints72.seeded_guards (CapturedGlobalEpoch64.prepared base n) legal)
theorem completed_outside (base : Nat → F) (n column : Nat)
    (outside : column<22738 ∨ 200692≤column)
    (notVerifier : column≠1 ∧ column≠2 ∧ column≠copy)
    (notHints : ¬(49≤column ∧ column<135)) : completed base n column=base column := by
  change CapturedFullArithmetic52.completed (prepared base n) column=base column
  rw [CapturedFullArithmetic52.outside (prepared base n) column outside]
  change CapturedRegisteredHints72.seeded (CapturedEpochHints62.seeded (CompilerVerifierLinks53.seeded base) n) column=base column
  rw [CapturedRegisteredHints72.seeded_outside _ column (by omega),
    CapturedEpochHints62.seeded_outside _ n column (by omega),
    CompilerVerifierLinks53.seeded_outside base column ⟨notVerifier.2.2,notVerifier.1,notVerifier.2.1⟩]
variable [CharP F p]
theorem completed_arithmetic (base : Nat → F) (n : Nat) :
    CompilerArithmeticBlock44.SatisfiesAt (completed base n) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedFullArithmetic52.complete (prepared base n)
theorem full_forbidden_pair (rho : Nat → F) (zero : rho 0=1)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (pair : Nat) (bound : pair<5) :
    eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair))=0 ∧
    eval rho (CapturedRegisteredAudit70.zeroTerms (2*pair+1))=0 → rho 10=0 :=
  CapturedRegisteredAudit71.forbidden_pair rho zero (CapturedFullRelation58.verifier_links rho sat).2.2
    (full_arithmetic_rows rho sat) (full_assertion_rows rho sat) pair bound
theorem completed_registered_assertions (base : Nat → F) (n : Nat) (zero : base 0=1)
    (legal : CapturedRegisteredHints72.LegalGuards (CapturedGlobalEpoch64.prepared base n)) :
    SatisfiesAt (completed base n) CapturedRegisteredAudit70.block.actual 35 :=
  CapturedRegisteredAssertions73.primitive_assertions (completed base n) (completed_zero base n zero)
    (completed_copy base n)
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 262 60
      CapturedRegisteredAudit70.arithmetic (Bool.and_eq_true_iff.mp arithmetic_checked).2 (by decide)
      (completed base n) (completed_arithmetic base n))
    (completed_primitive base n) (completed_guards base n legal)
theorem completed_epoch_assertions (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) (legalGuard : base 34=0 → base 10=0) (zero : base 0=1) :
    SatisfiesAt (completed base n) CapturedEpochRange60.block.actual 65 ∧
    SatisfiesAt (completed base n) CapturedEpochNonzero61.assertionBlock.actual 4 := by
  have epoch:=CompilerVerifierLinks53.seeded_outside base 34 (by decide)
  have regulated:=CompilerVerifierLinks53.seeded_outside base 10 (by decide)
  have rows:=CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 256 6
    CapturedEpochNonzero61.arithmetic (Bool.and_eq_true_iff.mp CapturedGlobalEpoch64.arithmetic_checked).2
    (by decide) (completed base n) (completed_arithmetic base n)
  exact CapturedEpochHints62.after_arithmetic_assertions (CompilerVerifierLinks53.seeded base) (completed base n) n
    bound (epoch.trans meaning) (fun h => regulated.trans (legalGuard (epoch.symm.trans h)))
    (completed_hint_agreement base n) (completed_zero base n zero) (completed_copy base n) rows
theorem completed_global104 (base : Nat → F) (n : Nat) (bound : n<2^64)
    (meaning : base 34=(n : F)) (legalGuard : base 34=0 → base 10=0) (zero : base 0=1)
    (coordinateGuards : CapturedRegisteredHints72.LegalGuards (CapturedGlobalEpoch64.prepared base n)) :
    SatisfiesAt (completed base n) (fun index => CapturedFullRelation58.rowAt (177979+index)) 104 :=
  selected_global104 (completed base n)
    (completed_epoch_assertions base n bound meaning legalGuard zero).1
    (completed_epoch_assertions base n bound meaning legalGuard zero).2
    (completed_registered_assertions base n zero coordinateGuards)
end ShielddSecurity.CapturedGlobalRegistered74
