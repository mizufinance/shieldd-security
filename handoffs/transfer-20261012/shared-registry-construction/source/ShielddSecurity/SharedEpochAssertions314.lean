import ShielddSecurity.SharedEpochZero311
import ShielddSecurity.CandidateEpoch315
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedEpochAssertions314
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310 SharedEpochZero311
theorem completed_primitive (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    CapturedEpochNonzero61.Primitive (HeaderRegisteredConstruction310.completed original c w initial) := by
  exact EpochSelectiveFrame313.primitive_frame (prepared original c w)
    (HeaderRegisteredConstruction310.completed original c w initial)
    (completed_epoch original c w initial) (completed_control original c w initial)
    (completed_indicator original c w initial legal) (completed_inverse original c w initial)
    (prepared_primitive original c w legal)

set_option pp.all true in
#check @ShielddSecurity.SharedEpochAssertions314.completed_primitive
#print axioms ShielddSecurity.SharedEpochAssertions314.completed_primitive

theorem completed_assertions (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (HeaderRegisteredConstruction310.completed original c w initial) CapturedEpochNonzero61.assertionBlock.actual 4 := by
  let seed := SharedWordWitness221.seeded
    (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
    (normalized (numbers original c w)) (fallback original c w)
  have one : seed 0 = 1 :=
    (SharedWordWitness221.seeded_fixed _ _ _).1.trans
      ((CapturedFourSubgroupSeed89.seeded_outside _ initial 0 (by decide)).trans (prepared_zero original c w))
  exact CandidateEpoch315.assertions seed one (completed_primitive original c w initial legal)

set_option pp.all true in
#check @ShielddSecurity.SharedEpochAssertions314.completed_assertions
#print axioms ShielddSecurity.SharedEpochAssertions314.completed_assertions

end ShielddSecurity.SharedEpochAssertions314
