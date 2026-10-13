import ShielddSecurity.SharedRegistryPrefix312
import ShielddSecurity.CapturedRegulatedAsset95
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedRegulatedValue316
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open WordHints210 LegalWordNormalization272 TransferSem RegisteredConstructorFrame309 HeaderRegisteredConstruction310

theorem original_frame (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (column : Nat)
    (preserved : RegistrySeedFrame265.Protected column)
    (group : column ∉ CapturedFourSubgroupSeed89.hintColumns) :
    HeaderRegisteredConstruction310.completed original c w initial column = prepared original c w column :=
  (RegistrySeedFrame265.completed_frame _ _ _ column preserved).trans
    (CapturedFourSubgroupSeed89.seeded_outside _ initial column group)

theorem asset_meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : HeaderRegisteredConstruction310.completed original c w initial 6 = (w.asset : F) :=
  (original_frame original c w initial 6 (by constructor <;> decide) (by decide)).trans
    ((prepared_outside original c w 6 (by decide) (by constructor <;> decide)).trans
      (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.1)

theorem registry_value_meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) : HeaderRegisteredConstruction310.completed original c w initial 11 = (w.registry.value : F) :=
  (original_frame original c w initial 11 (by constructor <;> decide) (by decide)).trans
    ((prepared_outside original c w 11 (by decide) (by constructor <;> decide)).trans
      (RegistryNaturalSeed298.seed_fixed _ _ 11 (by simp [RegistryNaturalSeed298.fixedColumns])))

theorem control_meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial 10 = (if w.regulated then 1 else 0) :=
  (SharedEpochZero311.completed_control original c w initial).trans
    ((prepared_outside original c w 10 (by decide) (by constructor <;> decide)).trans
      (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.2.2)

theorem regulated_assertion (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : RegistrySem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (HeaderRegisteredConstruction310.completed original c w initial)
      (fun index => CapturedFullRelation58.rowAt (178118+index)) 1 :=
  CapturedRegulatedAsset95.legal_assertion (crypto c) w legal
    (HeaderRegisteredConstruction310.completed original c w initial)
    (SharedWordWitness221.arithmetic _ _ _) (asset_meaning original c w initial)
    (registry_value_meaning original c w initial) (control_meaning original c w initial)
end ShielddSecurity.SharedRegulatedValue316

set_option pp.all true in
#check @ShielddSecurity.SharedRegulatedValue316.original_frame
#print axioms ShielddSecurity.SharedRegulatedValue316.original_frame

set_option pp.all true in
#check @ShielddSecurity.SharedRegulatedValue316.asset_meaning
#print axioms ShielddSecurity.SharedRegulatedValue316.asset_meaning

set_option pp.all true in
#check @ShielddSecurity.SharedRegulatedValue316.registry_value_meaning
#print axioms ShielddSecurity.SharedRegulatedValue316.registry_value_meaning

set_option pp.all true in
#check @ShielddSecurity.SharedRegulatedValue316.control_meaning
#print axioms ShielddSecurity.SharedRegulatedValue316.control_meaning

set_option pp.all true in
#check @ShielddSecurity.SharedRegulatedValue316.regulated_assertion
#print axioms ShielddSecurity.SharedRegulatedValue316.regulated_assertion
