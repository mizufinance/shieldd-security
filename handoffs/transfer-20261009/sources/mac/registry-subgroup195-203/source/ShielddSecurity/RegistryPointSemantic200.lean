import ShielddSecurity.CapturedSubgroupModel199
import ShielddSecurity.RegistryRecovery194
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryPointSemantic200
open PoseidonNatural192
variable {F J : Type} [Field F] [AddCommGroup J]
def encode (representation : CanonicalRepresentation F) (point : Group.Point F) : TransferCore.Affine :=
 ⟨representation.value point.x,representation.value point.y⟩
def interpret (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) : TransferSem.Crypto :=
 {c with subgroup:=fun point => ∃ represented : J,
   encode representation (model.coordinates represented)=point ∧ TransferCore.scalarOrder • represented=0}
theorem valid_of_member (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) (point : Group.Point F)
 (member : CapturedSubgroupModel199.Member model point) :
 TransferSem.ValidPoint (interpret c representation model) (encode representation point) := by
 rcases member with ⟨represented,coordinates,killed⟩
 refine ⟨⟨representation.bounded _,representation.bounded _⟩,represented,?_,killed⟩
 exact congrArg (encode representation) coordinates
variable [CharP F TransferFirstSubgroupData01.p]
theorem registry_points (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (rho : Nat → F) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0) :
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).detection ∧
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).ring ∧
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).audit.payload ∧
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).audit.checking := by
 rcases CapturedSubgroupModel199.captured_four rho one satisfied imaginary nonSquare imaginarySquare model standardOrder with ⟨a,b,c,d⟩
 exact ⟨valid_of_member _ representation model _ a,valid_of_member _ representation model _ b,
   valid_of_member _ representation model _ c,valid_of_member _ representation model _ d⟩
end ShielddSecurity.RegistryPointSemantic200

set_option pp.all true in
#check @ShielddSecurity.RegistryPointSemantic200.encode
#print axioms ShielddSecurity.RegistryPointSemantic200.encode
set_option pp.all true in
#check @ShielddSecurity.RegistryPointSemantic200.interpret
#print axioms ShielddSecurity.RegistryPointSemantic200.interpret
set_option pp.all true in
#check @ShielddSecurity.RegistryPointSemantic200.valid_of_member
#print axioms ShielddSecurity.RegistryPointSemantic200.valid_of_member
set_option pp.all true in
#check @ShielddSecurity.RegistryPointSemantic200.registry_points
#print axioms ShielddSecurity.RegistryPointSemantic200.registry_points
