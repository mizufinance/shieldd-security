import ShielddSecurity.MerkleNaturalRoot197
import ShielddSecurity.RegistryPointSemantic200
import ShielddSecurity.RegistryConditions201
import ShielddSecurity.RegistryExclusions204
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistrySemanticSound205
open PoseidonNatural192 RegistryRecovery194
open CompilerArithmeticTransport41 (p)
variable {F J : Type} [Field F] [AddCommGroup J]
def crypto (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) : TransferSem.Crypto :=
 withHash (RegistryPointSemantic200.interpret
   {c with unregulatedRing:=CapturedRegistryPointDomain75.sink} representation model)
   RegistryNatural193.small RegistryNatural193.wide representation
def witness (template : TransferSem.Witness) (representation : CanonicalRepresentation F)
 (rho : Nat → F) (flag : Bool) : TransferSem.Witness :=
 {template with registry:=recover representation rho,asset:=representation.value (rho 6),
 assetAnchor:=representation.value (rho 4),regulated:=flag}
variable [CharP F p]
theorem full_registry (c : TransferSem.Crypto) (template : TransferSem.Witness)
 (representation : CanonicalRepresentation F) (rho : Nat → F) (flag : Bool)
 (flagMeaning : rho 10=(if flag then 1 else 0)) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0) :
 TransferSem.RegistrySem (crypto c representation model) (witness template representation rho flag) := by
 have points:=RegistryPointSemantic200.registry_points
   {c with unregulatedRing:=CapturedRegistryPointDomain75.sink} representation rho one satisfied
   imaginary nonSquare imaginarySquare model standardOrder
 have root:=MerkleNaturalRoot197.anchor representation rho
   (RegistryPointSemantic200.interpret {c with unregulatedRing:=CapturedRegistryPointDomain75.sink}
     representation model) one satisfied
 have bounds:=RegistryConditions201.value_bounds representation rho
 refine ⟨points.1,points.2.1,points.2.2.1,points.2.2.2,
   RegistryConditions201.epoch_bound representation rho satisfied,root.1,
   bounds.1,bounds.2.1,bounds.2.2,root.2,?_⟩
 cases flag with
 | false =>
   exact RegistryConditions201.unregulated_order representation rho one satisfied flagMeaning
 | true =>
   have notZero : rho 10≠0 := by rw [flagMeaning];exact one_ne_zero
   have guards:=RegistryExclusions204.all_guards representation rho one satisfied notZero
   exact ⟨RegistryConditions201.regulated_value representation rho one satisfied flagMeaning,
     RegistryConditions201.epoch_nonzero representation rho one satisfied notZero,
     guards.1,guards.2.1,guards.2.2.1,guards.2.2.2.1,guards.2.2.2.2⟩
theorem exists_flag (rho : Nat → F) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ flag : Bool,rho 10=(if flag then 1 else 0) := by
 rcases CapturedRegulatedSound163.role_cases rho satisfied one with zero|oneFlag
 · exact ⟨false,zero⟩
 · exact ⟨true,oneFlag⟩
end ShielddSecurity.RegistrySemanticSound205

set_option pp.all true in
#check @ShielddSecurity.RegistrySemanticSound205.crypto
#print axioms ShielddSecurity.RegistrySemanticSound205.crypto
set_option pp.all true in
#check @ShielddSecurity.RegistrySemanticSound205.witness
#print axioms ShielddSecurity.RegistrySemanticSound205.witness
set_option pp.all true in
#check @ShielddSecurity.RegistrySemanticSound205.full_registry
#print axioms ShielddSecurity.RegistrySemanticSound205.full_registry
set_option pp.all true in
#check @ShielddSecurity.RegistrySemanticSound205.exists_flag
#print axioms ShielddSecurity.RegistrySemanticSound205.exists_flag
