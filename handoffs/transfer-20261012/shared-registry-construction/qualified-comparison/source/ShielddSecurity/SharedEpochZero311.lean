import ShielddSecurity.HeaderRegisteredConstruction310
import ShielddSecurity.EpochSelectiveFrame313
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedEpochZero311
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

theorem prepared_primitive (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem (crypto c) w) : CapturedEpochNonzero61.Primitive (prepared original c w) := by
  have guard := CapturedRegistryEpoch66.registry_guard (crypto c) w legal
    (HeaderRegistrySeed299.combined original c w)
    (RegistryNaturalSeed298.seed_fixed _ _ 34 (by simp [RegistryNaturalSeed298.fixedColumns]))
    (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.2.2
  have linked_guard : CompilerVerifierLinks53.seeded (HeaderRegistrySeed299.combined original c w) 34 = 0 →
      CompilerVerifierLinks53.seeded (HeaderRegistrySeed299.combined original c w) 10 = 0 := by
    intro zero
    have epoch := CompilerVerifierLinks53.seeded_outside (HeaderRegistrySeed299.combined original c w) 34 (by decide)
    have control := CompilerVerifierLinks53.seeded_outside (HeaderRegistrySeed299.combined original c w) 10 (by decide)
    exact control.trans (guard (epoch.symm.trans zero))
  have primitive := CapturedEpochHints62.seeded_primitive
    (CompilerVerifierLinks53.seeded (HeaderRegistrySeed299.combined original c w)) w.registry.audit.epoch linked_guard
  change CapturedEpochNonzero61.Primitive (HeaderRegisteredLegality307.base original c w) at primitive
  unfold CapturedEpochNonzero61.Primitive at primitive ⊢
  have frame (column : Nat) (outside : ¬(115 ≤ column ∧ column < 135)) :
      prepared original c w column = HeaderRegisteredLegality307.base original c w column :=
    CapturedRegisteredHints72.seeded_outside _ column outside
  rw [frame 113 (by decide),frame 114 (by decide),frame 34 (by decide),frame 10 (by decide)]
  exact primitive


set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.prepared_primitive
#print axioms ShielddSecurity.SharedEpochZero311.prepared_primitive

theorem prepared_indicator (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem (crypto c) w) : prepared original c w 113 = 0 ∨ prepared original c w 113 = 1 := by
  have equal := CapturedEpochNonzero61.primitive_zero _ (prepared_primitive original c w legal)
  by_cases zero : prepared original c w 34 = 0
  · right; exact equal.trans (if_pos zero)
  · left; exact equal.trans (if_neg zero)


set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.prepared_indicator
#print axioms ShielddSecurity.SharedEpochZero311.prepared_indicator

theorem stage_equal (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial = SharedRegisteredGeneral308.completed
      (CapturedFourSubgroupSeed89.seeded (HeaderRegisteredLegality307.base original c w) initial)
      (normalized (numbers original c w)) (fallback original c w) := by
  unfold HeaderRegisteredConstruction310.completed SharedRegisteredGeneral308.completed SharedRegisteredGeneral308.seeded
    SharedRegisteredGeneral308.prepared prepared
  rw [commute]
  rfl

set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.stage_equal
#print axioms ShielddSecurity.SharedEpochZero311.stage_equal

theorem completed_control (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : HeaderRegisteredConstruction310.completed original c w initial 10 = prepared original c w 10 := by
  rw [stage_equal]
  unfold SharedRegisteredGeneral308.completed
  rw [SharedRegisteredGeneral308.candidate_original _ 10 (by decide) (by decide)]
  have frame := SharedRegisteredGeneral308.control_seeded
    (CapturedFourSubgroupSeed89.seeded (HeaderRegisteredLegality307.base original c w) initial)
    (normalized (numbers original c w)) (fallback original c w)
    (fallback_agrees (HeaderRegisteredLegality307.base original c w) initial (numbers original c w))
    (by rw [CapturedFourSubgroupSeed89.seeded_outside _ initial 10 (by decide)]
        exact HeaderRegisteredLegality307.base_control original c w)
  exact frame.trans (by
    unfold SharedRegisteredGeneral308.prepared
    rw [commute,CapturedFourSubgroupSeed89.seeded_outside _ initial 10 (by decide)]
    rfl)

set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.completed_control
#print axioms ShielddSecurity.SharedEpochZero311.completed_control

theorem completed_indicator (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    HeaderRegisteredConstruction310.completed original c w initial 113 = prepared original c w 113 := by
  rw [stage_equal]
  unfold SharedRegisteredGeneral308.completed
  rw [SharedRegisteredGeneral308.candidate_original _ 113 (by decide) (by decide)]
  have frame := SharedRegisteredGeneral308.hint_frame
    (CapturedFourSubgroupSeed89.seeded (HeaderRegisteredLegality307.base original c w) initial)
    (normalized (numbers original c w)) (fallback original c w)
    (fallback_agrees (HeaderRegisteredLegality307.base original c w) initial (numbers original c w))
    113 (by decide) (by decide) (by
      intro _
      unfold SharedRegisteredGeneral308.prepared
      rw [commute,CapturedFourSubgroupSeed89.seeded_outside _ initial 113 (by decide)]
      exact prepared_indicator original c w legal)
  exact frame.trans (by
    unfold SharedRegisteredGeneral308.prepared
    rw [commute,CapturedFourSubgroupSeed89.seeded_outside _ initial 113 (by decide)]
    rfl)


set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.completed_indicator
#print axioms ShielddSecurity.SharedEpochZero311.completed_indicator

theorem completed_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : HeaderRegisteredConstruction310.completed original c w initial 114 = prepared original c w 114 := by
  have unselected : (114 : Nat) ∉ SharedWordWitness221.seedColumns := by
    intro selected
    have odd := ZeroHintBooleanShape304.selected_odd 114 selected (by decide) (by decide)
    omega
  change CapturedFullRelation58.candidate
    (SharedWordWitness221.seeded (CapturedFourSubgroupSeed89.seeded (prepared original c w) initial)
      (normalized (numbers original c w)) (fallback original c w)) 114 = prepared original c w 114
  exact (SharedRegisteredGeneral308.candidate_original _ 114 (by decide) (by decide)).trans
    ((BooleanHints207.seeded_outside _ _ _ 114 unselected).trans
      (CapturedFourSubgroupSeed89.seeded_outside _ initial 114 (by decide)))


set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.completed_inverse
#print axioms ShielddSecurity.SharedEpochZero311.completed_inverse

theorem completed_epoch (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : HeaderRegisteredConstruction310.completed original c w initial 34 = prepared original c w 34 :=
  (RegistrySeedFrame265.completed_frame _ _ _ 34 (by constructor <;> decide)).trans
    (CapturedFourSubgroupSeed89.seeded_outside _ initial 34 (by decide))


set_option pp.all true in
#check @ShielddSecurity.SharedEpochZero311.completed_epoch
#print axioms ShielddSecurity.SharedEpochZero311.completed_epoch

end ShielddSecurity.SharedEpochZero311
