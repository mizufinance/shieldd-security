import ShielddSecurity.CapturedRegistryEpoch66
import ShielddSecurity.CapturedZeroTests67
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGlobalZeroCompletion68
open CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def checkArithmetic : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 262 8 CapturedZeroTests67.arithmetic &&
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 262 8 CapturedZeroTests67.arithmetic
theorem arithmetic_checked : checkArithmetic=true := by decide +kernel
noncomputable def checkAssertions : Bool :=
  CompilerRowSlice63.check CapturedFullRelation58.rowAt 178048 6 CapturedZeroTests67.assertions &&
  CompilerRowSlice63.check CapturedZeroTests67.block.actual 0 6 CapturedZeroTests67.assertions
theorem assertions_checked : checkAssertions=true := by decide +kernel
variable {F : Type} [Field F]
theorem full_arithmetic_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho CapturedZeroTests67.arithmetic :=
  CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt 200770 262 8
    CapturedZeroTests67.arithmetic (Bool.and_eq_true_iff.mp arithmetic_checked).1 (by decide) rho sat
theorem full_assertion_rows (rho : Nat → F)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : SatisfiesAt rho CapturedZeroTests67.block.actual 6 := by
  have checks:=Bool.and_eq_true_iff.mp assertions_checked
  have rows:=CompilerRowSlice63.of_full_satisfies CapturedFullRelation58.rowAt 200770 178048 6
    CapturedZeroTests67.assertions checks.1 (by decide) rho sat
  have localRows:=(CompilerRowSlice63.selected_satisfies_iff CapturedZeroTests67.block.actual 0 6
    CapturedZeroTests67.assertions checks.2 rho).mp rows
  simpa only [Nat.zero_add] using localRows
noncomputable def prepared (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedZeroTests67.seeded (CapturedGlobalEpoch64.prepared base n)
noncomputable def completed (base : Nat → F) (n : Nat) : Nat → F :=
  CapturedFullArithmetic52.completed (prepared base n)
theorem prepared_zero (base : Nat → F) (n : Nat) : prepared base n 0=base 0 :=
  (CapturedZeroTests67.seeded_outside _ 0 (by decide)).trans
    ((CapturedEpochHints62.seeded_outside _ n 0 (by decide)).trans
      (CompilerVerifierLinks53.seeded_outside base 0 (by decide)))
theorem prepared_copy (base : Nat → F) (n : Nat) : prepared base n copy=prepared base n 0 := by
  calc
    prepared base n copy = CapturedGlobalEpoch64.prepared base n copy := CapturedZeroTests67.seeded_outside _ copy (by decide)
    _ = CompilerVerifierLinks53.seeded base copy := CapturedEpochHints62.seeded_outside _ n copy (by decide)
    _ = CompilerVerifierLinks53.seeded base 0 := CompilerVerifierLinks53.seeded_copy base
    _ = CapturedGlobalEpoch64.prepared base n 0 := (CapturedEpochHints62.seeded_outside _ n 0 (by decide)).symm
    _ = prepared base n 0 := (CapturedZeroTests67.seeded_outside _ 0 (by decide)).symm
theorem completed_hint_agreement (base : Nat → F) (n : Nat) :
    CapturedEpochHints62.HintAgreement (CapturedGlobalEpoch64.prepared base n) (completed base n) := by
  intro column bound
  exact (CapturedZeroTests67.seeded_outside _ column (by omega)).symm.trans
    (CapturedFullArithmetic52.outside (prepared base n) column (Or.inl (by omega))).symm
theorem completed_zero (base : Nat → F) (n : Nat) (zero : base 0=1) : completed base n 0=1 :=
  (CapturedFullArithmetic52.fixed (prepared base n)).1.trans ((prepared_zero base n).trans zero)
theorem completed_copy (base : Nat → F) (n : Nat) : completed base n copy=completed base n 0 :=
  ((CapturedFullArithmetic52.fixed (prepared base n)).2.2.2.trans (prepared_copy base n)).trans
    (CapturedFullArithmetic52.fixed (prepared base n)).1.symm
theorem completed_primitive (base : Nat → F) (n : Nat) : CapturedZeroTests67.Primitive (completed base n) := by
  have agreement : ∀ column<119,completed base n column=prepared base n column := fun column bound =>
    CapturedFullArithmetic52.outside (prepared base n) column (Or.inl (by omega))
  unfold CapturedZeroTests67.Primitive
  rw [agreement 35 (by decide),agreement 115 (by decide),agreement 116 (by decide),
    agreement 36 (by decide),agreement 0 (by decide),agreement 117 (by decide),agreement 118 (by decide)]
  exact CapturedZeroTests67.seeded_primitive (CapturedGlobalEpoch64.prepared base n)
variable [CharP F p]
theorem full_primitive (rho : Nat → F) (zero : rho 0=1)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : CapturedZeroTests67.Primitive rho :=
  CapturedZeroTests67.actual_primitive rho zero (CapturedFullRelation58.verifier_links rho sat).2.2
    (full_arithmetic_rows rho sat) (full_assertion_rows rho sat)
theorem full_zero_meanings (rho : Nat → F) (zero : rho 0=1)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    rho 115=CompilerZeroTest65.indicator (rho 35) ∧ rho 117=CompilerZeroTest65.indicator (rho 36-1) := by
  have primitive:=full_primitive rho zero sat
  exact ⟨CompilerZeroTest65.indicator_sound _ _ _ primitive.1,
    by simpa only [zero] using CompilerZeroTest65.indicator_sound _ _ _ primitive.2⟩
theorem completed_arithmetic (base : Nat → F) (n : Nat) :
    CompilerArithmeticBlock44.SatisfiesAt (completed base n) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedFullArithmetic52.complete (prepared base n)
theorem completed_zero_assertions (base : Nat → F) (n : Nat) (zero : base 0=1) :
    SatisfiesAt (completed base n) CapturedZeroTests67.block.actual 6 :=
  CapturedZeroTests67.primitive_assertions (completed base n) (completed_zero base n zero) (completed_copy base n)
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 262 8
      CapturedZeroTests67.arithmetic (Bool.and_eq_true_iff.mp arithmetic_checked).2 (by decide)
      (completed base n) (completed_arithmetic base n)) (completed_primitive base n)
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
theorem legal_registry_assertions (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem c w) (base : Nat → F)
    (epoch : base 34=(w.registry.audit.epoch : F))
    (regulated : base 10=(if w.regulated then 1 else 0)) (zero : base 0=1) :
    SatisfiesAt (completed base w.registry.audit.epoch) CapturedEpochRange60.block.actual 65 ∧
    SatisfiesAt (completed base w.registry.audit.epoch) CapturedEpochNonzero61.assertionBlock.actual 4 ∧
    SatisfiesAt (completed base w.registry.audit.epoch) CapturedZeroTests67.block.actual 6 :=
  ⟨(completed_epoch_assertions base w.registry.audit.epoch (CapturedRegistryEpoch66.registry_epoch_bound c w legal)
      epoch (CapturedRegistryEpoch66.registry_guard c w legal base epoch regulated) zero).1,
    (completed_epoch_assertions base w.registry.audit.epoch (CapturedRegistryEpoch66.registry_epoch_bound c w legal)
      epoch (CapturedRegistryEpoch66.registry_guard c w legal base epoch regulated) zero).2,
    completed_zero_assertions base w.registry.audit.epoch zero⟩
theorem completed_outside (base : Nat → F) (n column : Nat)
    (arithmeticOutside : column<22738 ∨ 200692≤column)
    (epochOutside : column<49 ∨ 115≤column)
    (zeroOutside : column≠115 ∧ column≠116 ∧ column≠117 ∧ column≠118)
    (verifierOutside : column≠copy ∧ column≠1 ∧ column≠2) : completed base n column=base column :=
  (CapturedFullArithmetic52.outside (prepared base n) column arithmeticOutside).trans
    ((CapturedZeroTests67.seeded_outside _ column zeroOutside).trans
      ((CapturedEpochHints62.seeded_outside _ n column epochOutside).trans
        (CompilerVerifierLinks53.seeded_outside base column verifierOutside)))
end ShielddSecurity.CapturedGlobalZeroCompletion68
