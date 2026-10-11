import ShielddSecurity.SubgroupPreimage202
import ShielddSecurity.RegistryPointSemantic200
import ShielddSecurity.CapturedFourSubgroupSeed89
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SubgroupSeedCompletion203
open PoseidonNatural192
variable {F J : Type} [Field F] [AddCommGroup J]
def fieldPoint (point : TransferCore.Affine) : Group.Point F := ⟨(point.x:F),(point.y:F)⟩
theorem member_of_valid (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) (point : TransferCore.Affine)
 (valid : TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) point) :
 CapturedSubgroupModel199.Member model (fieldPoint point) := by
 rcases valid.2 with ⟨represented,encoded,killed⟩
 refine ⟨represented,?_,killed⟩
 have hx : (model.coordinates represented).x=(fieldPoint point).x := by
   have same:=congrArg TransferCore.Affine.x encoded
   exact (representation.cast_value _).symm.trans (congrArg (fun n : Nat => (n:F)) same)
 have hy : (model.coordinates represented).y=(fieldPoint point).y := by
   have same:=congrArg TransferCore.Affine.y encoded
   exact (representation.cast_value _).symm.trans (congrArg (fun n : Nat => (n:F)) same)
 cases model.coordinates represented
 exact congrArg₂ Group.Point.mk hx hy
theorem exists_initial (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (base : Nat → F)
 (members : ∀ group,CapturedSubgroupModel199.Member model (CapturedFourSubgroupSeed89.Claimed base group)) :
 ∃ initial : Fin 4 → Group.Point F,
 (∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group)) ∧
 ∀ group,CapturedFourSubgroupSeed89.Claimed base group=
   CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group) := by
 classical
 have preimages:=fun group => SubgroupPreimage202.member_preimage (CapturedFirstSubgroup81.d:F)
   imaginary nonSquare imaginarySquare model _ (members group)
 refine ⟨fun group => Classical.choose (preimages group),?_,?_⟩
 · intro group
   exact (Classical.choose_spec (preimages group)).1
 · intro group
   exact (Classical.choose_spec (preimages group)).2.symm
variable [CharP F TransferFirstSubgroupData01.p]
theorem constructor (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (base : Nat → F)
 (one : base 0=1) (linked : base TransferFirstSubgroupData01.copy=base 0)
 (members : ∀ group,CapturedSubgroupModel199.Member model (CapturedFourSubgroupSeed89.Claimed base group)) :
 ∃ initial : Fin 4 → Group.Point F,
 CompilerArithmeticBlock44.SatisfiesAt (CapturedFourSubgroupSeed89.completed base initial)
   CapturedFullArithmetic52.rowAt 177954 ∧
 (∀ group,Satisfies (CapturedFourSubgroupSeed89.completed base initial)
   (CapturedFourSubgroupConstructor88.originalRows group)) ∧
 ∀ column,(column<22738 ∨ 200692≤column) → column∉CapturedFourSubgroupSeed89.hintColumns →
   CapturedFourSubgroupSeed89.completed base initial column=base column := by
 obtain ⟨initial,valid,binding⟩:=exists_initial model imaginary nonSquare imaginarySquare base members
 exact ⟨initial,CapturedFourSubgroupSeed89.arithmetic base initial,
   CapturedFourSubgroupSeed89.all_four base initial imaginary one linked binding valid nonSquare imaginarySquare,
   fun column outside unseeded => CapturedFourSubgroupSeed89.outside base initial column outside unseeded⟩
end ShielddSecurity.SubgroupSeedCompletion203

set_option pp.all true in
#check @ShielddSecurity.SubgroupSeedCompletion203.fieldPoint
#print axioms ShielddSecurity.SubgroupSeedCompletion203.fieldPoint
set_option pp.all true in
#check @ShielddSecurity.SubgroupSeedCompletion203.member_of_valid
#print axioms ShielddSecurity.SubgroupSeedCompletion203.member_of_valid
set_option pp.all true in
#check @ShielddSecurity.SubgroupSeedCompletion203.exists_initial
#print axioms ShielddSecurity.SubgroupSeedCompletion203.exists_initial
set_option pp.all true in
#check @ShielddSecurity.SubgroupSeedCompletion203.constructor
#print axioms ShielddSecurity.SubgroupSeedCompletion203.constructor
