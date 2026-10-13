import ShielddSecurity.ComparisonConstruction328
import ShielddSecurity.FieldZeroSeed125
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HighZeroSeed329
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def firstDelta (w : TransferSem.Witness) : F :=
  (RegistryComparisonSeed318.high w.asset:F)-(RegistryComparisonSeed318.high w.registry.value:F)
def secondDelta (w : TransferSem.Witness) : F :=
  (RegistryComparisonSeed318.high w.registry.nextValue:F)-(RegistryComparisonSeed318.high w.asset:F)
def seed (original : Nat → F) (w : TransferSem.Witness) : Nat → F :=
  FieldZeroSeed125.seeded (FieldZeroSeed125.seeded original 1110 (firstDelta w)) 1371 (secondDelta w)

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (first : column<1110 ∨1112≤column) (second : column<1371 ∨1373≤column) :
    seed original w column=original column :=
  (FieldZeroSeed125.outside _ 1371 (secondDelta w) column second).trans
    (FieldZeroSeed125.outside original 1110 (firstDelta w) column first)

theorem first_flag (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 1110=FieldZeroSeed125.flag (firstDelta w) :=
  (FieldZeroSeed125.outside _ 1371 (secondDelta w) 1110 (Or.inl (by decide))).trans
    (FieldZeroSeed125.flag_value original 1110 (firstDelta w))
theorem first_inverse (original : Nat → F) (w : TransferSem.Witness) : seed original w 1111=(firstDelta w)⁻¹ :=
  (FieldZeroSeed125.outside _ 1371 (secondDelta w) 1111 (Or.inl (by decide))).trans
    (FieldZeroSeed125.inverse_value original 1110 (firstDelta w))
theorem second_flag (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 1371=FieldZeroSeed125.flag (secondDelta w) :=
  FieldZeroSeed125.flag_value _ 1371 (secondDelta w)
theorem second_inverse (original : Nat → F) (w : TransferSem.Witness) : seed original w 1372=(secondDelta w)⁻¹ :=
  FieldZeroSeed125.inverse_value _ 1371 (secondDelta w)
end ShielddSecurity.HighZeroSeed329

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.firstDelta
#print axioms ShielddSecurity.HighZeroSeed329.firstDelta

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.secondDelta
#print axioms ShielddSecurity.HighZeroSeed329.secondDelta

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.seed
#print axioms ShielddSecurity.HighZeroSeed329.seed

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.outside
#print axioms ShielddSecurity.HighZeroSeed329.outside

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.first_flag
#print axioms ShielddSecurity.HighZeroSeed329.first_flag

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.first_inverse
#print axioms ShielddSecurity.HighZeroSeed329.first_inverse

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.second_flag
#print axioms ShielddSecurity.HighZeroSeed329.second_flag

set_option pp.all true in
#check @ShielddSecurity.HighZeroSeed329.second_inverse
#print axioms ShielddSecurity.HighZeroSeed329.second_inverse
