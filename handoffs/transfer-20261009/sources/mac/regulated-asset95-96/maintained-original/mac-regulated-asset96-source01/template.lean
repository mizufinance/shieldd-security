import ShielddSecurity.CapturedRegulatedAsset95
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegulatedAsset96
open CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F]
theorem outside_early (base : Nat → F) (initial : Fin 4 → Group.Point F) (epoch position column : Nat)
    (before : column<49) (notVerifier : column≠1 ∧ column≠2 ∧ column≠copy)
    (notSeed : column∉CapturedFourSubgroupSeed89.hintColumns) :
    CapturedGlobalSubgroup90.completed base initial epoch position column=base column := by
  have arith : column<22738 := Nat.lt_trans before (by decide)
  have pos : column<184 := Nat.lt_trans before (by decide)
  have epochHint : ¬(49≤column ∧ column<135) := fun h => (Nat.not_le_of_gt before) h.1
  exact (CapturedGlobalPosition77.outside (CapturedFourSubgroupSeed89.seeded base initial) epoch position column
    (Or.inl arith) notVerifier epochHint (Or.inl pos)).trans
      (CapturedFourSubgroupSeed89.seeded_outside base initial column notSeed)
variable [CharP F p]
theorem legal_zero (c : TransferSem.Crypto) (w : TransferSem.Witness) (legal : TransferSem.RegistrySem c w)
    (base : Nat → F) (initial : Fin 4 → Group.Point F)
    (asset : base 6=(w.asset:F)) (registry : base 11=(w.registry.value:F))
    (regulated : base 10=(if w.regulated then 1 else 0)) :
    SatisfiesAt (CapturedGlobalSubgroup90.completed base initial w.registry.audit.epoch w.registry.position)
      (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 := by
  have arithmetic : SatisfiesAt
      (CapturedGlobalSubgroup90.completed base initial w.registry.audit.epoch w.registry.position)
      CapturedFullArithmetic52.rowAt 177954 :=
    CapturedGlobalRegistered74.completed_arithmetic
      (MerkleBits29.seed (CapturedFourSubgroupSeed89.seeded base initial) w.registry.position) w.registry.audit.epoch
  have six:=outside_early base initial w.registry.audit.epoch w.registry.position 6 (by decide) (by decide) (by decide)
  have eleven:=outside_early base initial w.registry.audit.epoch w.registry.position 11 (by decide) (by decide) (by decide)
  have ten:=outside_early base initial w.registry.audit.epoch w.registry.position 10 (by decide) (by decide) (by decide)
  exact CapturedRegulatedAsset95.legal_assertion c w legal _ arithmetic
    (six.trans asset) (eleven.trans registry) (ten.trans regulated)
end ShielddSecurity.CapturedRegulatedAsset96
