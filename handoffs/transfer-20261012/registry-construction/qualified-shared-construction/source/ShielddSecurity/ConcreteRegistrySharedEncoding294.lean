import ShielddSecurity.ConcreteCofactorModel01
import ShielddSecurity.RegistrySemanticSound205
import ShielddSecurity.LegalWordEncoding278
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ConcreteRegistrySharedEncoding294
open ConcreteJubjubField01 ConcretePointTorsion01
open PoseidonNatural192 WordHints210 LegalWordNormalization272

def representation : CanonicalRepresentation F where
  value := ZMod.val
  bounded := fun value => ZMod.val_lt value
  cast_value := fun value => ZMod.natCast_zmod_val value

theorem coefficient_eq : (CapturedFirstSubgroup81.d : F) = ConcreteJubjubField01.coefficient := by
  simp only [CapturedFirstSubgroup81.d, ConcreteJubjubField01.coefficient,
    ConcreteJubjubField01.coefficientNat, Int.cast_ofNat, Nat.cast_ofNat]

def model : Group.StandardCurveModel curve.Point (CapturedFirstSubgroup81.d : F) := by
  rw [coefficient_eq]
  exact ConcreteCofactorModel01.model

theorem standard_order (point : curve.Point) : (8 * TransferCore.scalarOrder) • point = 0 :=
  ConcreteCofactorModel01.global_exponent point

def crypto (c : TransferSem.Crypto) : TransferSem.Crypto :=
  RegistrySemanticSound205.crypto c representation model

def witness (template : TransferSem.Witness) (rho : Nat → F) (flag : Bool) : TransferSem.Witness :=
  RegistrySemanticSound205.witness template representation rho flag

theorem registry_sound (c : TransferSem.Crypto) (template : TransferSem.Witness)
    (rho : Nat → F) (flag : Bool) (flagMeaning : rho 10 = (if flag then 1 else 0))
    (one : rho 0 = 1)
    (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    TransferSem.RegistrySem (crypto c) (witness template rho flag) := by
  exact RegistrySemanticSound205.full_registry c template representation rho flag flagMeaning one satisfied
    ConcreteJubjubField01.imaginary
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square)
    ConcreteJubjubField01.imaginary_square model standard_order

theorem registry_flag_and_semantics (c : TransferSem.Crypto) (template : TransferSem.Witness)
    (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    ∃ flag : Bool, rho 10 = (if flag then 1 else 0) ∧
      TransferSem.RegistrySem (crypto c) (witness template rho flag) := by
  obtain ⟨flag, meaning⟩ := RegistrySemanticSound205.exists_flag rho satisfied
  exact ⟨flag, meaning, registry_sound c template rho flag meaning one satisfied⟩

theorem legal_completed (c : TransferSem.Crypto) (base : Nat → F)
    (numbers : Nat → Nat) (old : Nat → Bool) (one : base 0 = 1)
    (otherBound : ∀ entry ∈ CapturedWordRoot213.words,
      ¬ Alias entry.1.value → numbers entry.1.value < 2 ^ entry.1.width)
    (original : ∀ entry ∈ CapturedWordRoot213.words,
      ¬ Alias entry.1.value → base entry.1.value = (numbers entry.1.value : F))
    (position : numbers 135 = representation.value (base 135)) (w : TransferSem.Witness)
    (legal : TransferSem.RegistrySem (crypto c) w)
    (registry : RegistryRecovery194.recover representation base = w.registry)
    (anchor : representation.value (base 4) = w.assetAnchor) :
    ∃ initial : Fin 4 → Group.Point F,
      LegalSharedRows271.Rows (SharedWordWitness221.completed
        (CapturedFourSubgroupSeed89.seeded base initial) (normalized numbers)
        (LegalAliasMeanings276.fallback numbers old)) ∧
      (∀ group, Satisfies (SharedWordWitness221.completed
        (CapturedFourSubgroupSeed89.seeded base initial) (normalized numbers)
        (LegalAliasMeanings276.fallback numbers old))
        (CapturedFourSubgroupConstructor88.originalRows group)) ∧
      ∃ row, CapturedFullRelation58.rowAt 178117 = some row ∧
        Square
          (eval (SharedWordWitness221.completed
            (CapturedFourSubgroupSeed89.seeded base initial) (normalized numbers)
            (LegalAliasMeanings276.fallback numbers old)) row.a)
          (eval (SharedWordWitness221.completed
            (CapturedFourSubgroupSeed89.seeded base initial) (normalized numbers)
            (LegalAliasMeanings276.fallback numbers old)) row.b) := by
  exact LegalWordEncoding278.legal_completed
    { c with unregulatedRing := CapturedRegistryPointDomain75.sink }
    representation model base ConcreteJubjubField01.imaginary
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square)
    ConcreteJubjubField01.imaginary_square numbers old one otherBound original position w legal registry anchor

end ShielddSecurity.ConcreteRegistrySharedEncoding294


set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.representation
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.representation

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.coefficient_eq
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.coefficient_eq

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.model
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.model

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.standard_order
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.standard_order

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.crypto
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.crypto

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.witness
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.witness

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.registry_sound
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.registry_sound

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.registry_flag_and_semantics
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.registry_flag_and_semantics

set_option pp.all true in
#check @ShielddSecurity.ConcreteRegistrySharedEncoding294.legal_completed
#print axioms ShielddSecurity.ConcreteRegistrySharedEncoding294.legal_completed
