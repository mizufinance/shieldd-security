import ShielddSecurity.CapturedGlobalEpoch64
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateEpoch315
open Compiler CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem assertions (base : Nat → F) (one : base 0 = 1)
    (primitive : CapturedEpochNonzero61.Primitive (CapturedFullRelation58.candidate base)) :
    CompilerAssertionBlock51.SatisfiesAt (CapturedFullRelation58.candidate base)
      CapturedEpochNonzero61.assertionBlock.actual 4 :=
  CapturedEpochNonzero61.primitive_assertions (CapturedFullRelation58.candidate base)
    ((CapturedFullRelation58.candidate_outside base 0 (Or.inl (by decide)) (by constructor <;> decide)).trans one)
    (CapturedFullRelation58.candidate_links base).2.2
    (CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 256 6
      CapturedEpochNonzero61.arithmetic (Bool.and_eq_true_iff.mp CapturedGlobalEpoch64.arithmetic_checked).2
      (by decide) (CapturedFullRelation58.candidate base) (CapturedFullRelation58.candidate_arithmetic base)) primitive
end ShielddSecurity.CandidateEpoch315
set_option pp.all true in
#check @ShielddSecurity.CandidateEpoch315.assertions
#print axioms ShielddSecurity.CandidateEpoch315.assertions
