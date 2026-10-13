import ShielddSecurity.ComparisonSeedFixed325
import ShielddSecurity.ComparisonDifferenceBits326
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedComparisonBlocks327
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) : Nat → F :=
  HeaderRegisteredConstruction310.completed (RegistryComparisonSeed318.seed original w) c w initial

theorem linked (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    assignment original c w initial copy=assignment original c w initial 0 :=
  (CapturedFullRelation58.candidate_links (SharedWordWitness221.seeded
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared (RegistryComparisonSeed318.seed original w) c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers (RegistryComparisonSeed318.seed original w) c w))
    (HeaderRegisteredConstruction310.fallback (RegistryComparisonSeed318.seed original w) c w))).2.2

theorem asset_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    fieldBinary ((List.range' (471+128) 127).map (assignment original c w initial)) = (RegistryComparisonSeed318.high (w.asset) : F) := by
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  exact HighBitMeaning122.high_meaning _ 471 (w.asset) (canon.1) (RegistryWordBits322.asset_bits original c w initial legal)

theorem asset_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    fieldBinary ((List.range' 471 128).map (assignment original c w initial)) = (RegistryComparisonSeed318.low (w.asset) : F) := by
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have meaning := LowBitMeaning128.low_meaning (assignment original c w initial) 471 (w.asset)
    (RegistryWordBits322.asset_bits original c w initial legal)
  rw [SharedWordLimbMeaning321.canonical_low (w.asset) (canon.1)] at meaning
  exact meaning

theorem value_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    fieldBinary ((List.range' (216+128) 127).map (assignment original c w initial)) = (RegistryComparisonSeed318.high (w.registry.value) : F) := by
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  exact HighBitMeaning122.high_meaning _ 216 (w.registry.value) (canon.2.1) (RegistryWordBits322.value_bits original c w initial legal)

theorem value_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    fieldBinary ((List.range' 216 128).map (assignment original c w initial)) = (RegistryComparisonSeed318.low (w.registry.value) : F) := by
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have meaning := LowBitMeaning128.low_meaning (assignment original c w initial) 216 (w.registry.value)
    (RegistryWordBits322.value_bits original c w initial legal)
  rw [SharedWordLimbMeaning321.canonical_low (w.registry.value) (canon.2.1)] at meaning
  exact meaning

theorem next_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    fieldBinary ((List.range' (726+128) 127).map (assignment original c w initial)) = (RegistryComparisonSeed318.high (w.registry.nextValue) : F) := by
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  exact HighBitMeaning122.high_meaning _ 726 (w.registry.nextValue) (canon.2.2) (RegistryWordBits322.next_bits original c w initial legal)

theorem next_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    fieldBinary ((List.range' 726 128).map (assignment original c w initial)) = (RegistryComparisonSeed318.low (w.registry.nextValue) : F) := by
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have meaning := LowBitMeaning128.low_meaning (assignment original c w initial) 726 (w.registry.nextValue)
    (RegistryWordBits322.next_bits original c w initial legal)
  rw [SharedWordLimbMeaning321.canonical_low (w.registry.nextValue) (canon.2.2)] at meaning
  exact meaning

theorem first_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (178893+index)) 130 := by
  let rho := assignment original c w initial
  let a := RegistryComparisonSeed318.high (w.asset)
  let b := RegistryComparisonSeed318.high (w.registry.value)
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have fixed := ComparisonSeedFixed325.first_high rho a b
    (ComparisonBorrowFrame324.completed_value original c w initial 981 (by decide))
    (CompletedComparisonValues323.first_high original c w initial)
    (ComparisonDifferenceBits326.first_high original c w initial legal.2.1.1)
  have satisfied := CapturedRegistryHighLimb121.full_complete rho a b
    (RegistryComparisonSeed318.high_bound _ canon.1) (RegistryComparisonSeed318.high_bound _ canon.2.1) (asset_high original c w initial legal) (value_high original c w initial legal)
    (linked original c w initial)
  rw [fixed] at satisfied
  exact satisfied

theorem first_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (179026+index)) 131 := by
  let rho := assignment original c w initial
  let a := RegistryComparisonSeed318.low (w.asset)
  let b := RegistryComparisonSeed318.low (w.registry.value)
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have fixed := ComparisonSeedFixed325.first_low rho a b
    (ComparisonBorrowFrame324.completed_value original c w initial 1112 (by decide))
    (CompletedComparisonValues323.first_low original c w initial)
    (ComparisonDifferenceBits326.first_low original c w initial legal.2.1.1)
  have satisfied := CapturedRegistryLowLimb130.full_complete rho a b
    (RegistryComparisonSeed318.low_bound _) (RegistryComparisonSeed318.low_bound _) (asset_low original c w initial legal) (value_low original c w initial legal)
    (linked original c w initial)
  rw [fixed] at satisfied
  exact satisfied

theorem second_high (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (179157+index)) 130 := by
  let rho := assignment original c w initial
  let a := RegistryComparisonSeed318.high (w.registry.nextValue)
  let b := RegistryComparisonSeed318.high (w.asset)
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have fixed := ComparisonSeedFixed325.second_high rho a b
    (ComparisonBorrowFrame324.completed_value original c w initial 1242 (by decide))
    (CompletedComparisonValues323.second_high original c w initial)
    (ComparisonDifferenceBits326.second_high original c w initial legal.2.1.1)
  have satisfied := CapturedNextHighLimb134.full_complete rho a b
    (RegistryComparisonSeed318.high_bound _ canon.2.2) (RegistryComparisonSeed318.high_bound _ canon.1) (next_high original c w initial legal) (asset_high original c w initial legal)
    (linked original c w initial)
  rw [fixed] at satisfied
  exact satisfied

theorem second_low (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (179290+index)) 131 := by
  let rho := assignment original c w initial
  let a := RegistryComparisonSeed318.low (w.registry.nextValue)
  let b := RegistryComparisonSeed318.low (w.asset)
  have canon := RegistryComparisonSeed318.canonical_values c w legal.2.1.1
  have fixed := ComparisonSeedFixed325.second_low rho a b
    (ComparisonBorrowFrame324.completed_value original c w initial 1373 (by decide))
    (CompletedComparisonValues323.second_low original c w initial)
    (ComparisonDifferenceBits326.second_low original c w initial legal.2.1.1)
  have satisfied := CapturedNextLowLimb141.full_complete rho a b
    (RegistryComparisonSeed318.low_bound _) (RegistryComparisonSeed318.low_bound _) (next_low original c w initial legal) (asset_low original c w initial legal)
    (linked original c w initial)
  rw [fixed] at satisfied
  exact satisfied

end ShielddSecurity.SharedComparisonBlocks327

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.assignment
#print axioms ShielddSecurity.SharedComparisonBlocks327.assignment

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.linked
#print axioms ShielddSecurity.SharedComparisonBlocks327.linked

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.asset_high
#print axioms ShielddSecurity.SharedComparisonBlocks327.asset_high

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.asset_low
#print axioms ShielddSecurity.SharedComparisonBlocks327.asset_low

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.value_high
#print axioms ShielddSecurity.SharedComparisonBlocks327.value_high

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.value_low
#print axioms ShielddSecurity.SharedComparisonBlocks327.value_low

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.next_high
#print axioms ShielddSecurity.SharedComparisonBlocks327.next_high

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.next_low
#print axioms ShielddSecurity.SharedComparisonBlocks327.next_low

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.first_high
#print axioms ShielddSecurity.SharedComparisonBlocks327.first_high

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.first_low
#print axioms ShielddSecurity.SharedComparisonBlocks327.first_low

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.second_high
#print axioms ShielddSecurity.SharedComparisonBlocks327.second_high

set_option pp.all true in
#check @ShielddSecurity.SharedComparisonBlocks327.second_low
#print axioms ShielddSecurity.SharedComparisonBlocks327.second_low
