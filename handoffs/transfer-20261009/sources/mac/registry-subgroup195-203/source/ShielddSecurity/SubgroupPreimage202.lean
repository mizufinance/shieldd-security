import ShielddSecurity.CapturedSubgroupModel199
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SubgroupPreimage202
open CompilerSubgroupArithmetic79
variable {F J : Type} [Field F] [AddCommGroup J]
def inverseEight : Nat := (TransferCore.scalarOrder+1)/8
theorem inverse_identity : 8*inverseEight=TransferCore.scalarOrder+1 := by
 unfold inverseEight TransferCore.scalarOrder
 decide +kernel
theorem pullback (point : J) (annihilated : TransferCore.scalarOrder • point=0) :
 (8:Nat) • (inverseEight • point)=point := by
 rw [←mul_nsmul,Nat.mul_comm inverseEight 8,inverse_identity,add_nsmul,annihilated,one_nsmul,zero_add]
theorem eight_coordinates (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (model : Group.StandardCurveModel J d)
 (point : J) : eight d (model.coordinates point)=model.coordinates ((8:Nat) • point) := by
 have valid:=model.onCurve point
 have first : model.coordinates (point+point)=trace d (model.coordinates point) 1 := by
   rw [model.addition]
   exact (CapturedSubgroupModel199.trace_affine d imaginary nonSquare imaginarySquare _ valid 0).symm
 have second : model.coordinates ((point+point)+(point+point))=trace d (model.coordinates point) 2 := by
   rw [model.addition,first]
   exact (CapturedSubgroupModel199.trace_affine d imaginary nonSquare imaginarySquare _ valid 1).symm
 have third : model.coordinates (((point+point)+(point+point))+((point+point)+(point+point)))=
   eight d (model.coordinates point) := by
   rw [model.addition,second]
   exact (CapturedSubgroupModel199.trace_affine d imaginary nonSquare imaginarySquare _ valid 2).symm
 have repeated : (((point+point)+(point+point))+((point+point)+(point+point)))=(8:Nat) • point := by
   simp only [←two_nsmul,←mul_nsmul]
 rw [repeated] at third
 exact third.symm
theorem member_preimage (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (model : Group.StandardCurveModel J d)
 (point : Group.Point F) (member : CapturedSubgroupModel199.Member model point) :
 ∃ preimage : Group.Point F,Group.OnCurve d preimage ∧ eight d preimage=point := by
 rcases member with ⟨represented,coordinates,annihilated⟩
 refine ⟨model.coordinates (inverseEight • represented),model.onCurve _,?_⟩
 rw [eight_coordinates d imaginary nonSquare imaginarySquare model,pullback represented annihilated]
 exact coordinates
end ShielddSecurity.SubgroupPreimage202

set_option pp.all true in
#check @ShielddSecurity.SubgroupPreimage202.inverseEight
#print axioms ShielddSecurity.SubgroupPreimage202.inverseEight
set_option pp.all true in
#check @ShielddSecurity.SubgroupPreimage202.inverse_identity
#print axioms ShielddSecurity.SubgroupPreimage202.inverse_identity
set_option pp.all true in
#check @ShielddSecurity.SubgroupPreimage202.pullback
#print axioms ShielddSecurity.SubgroupPreimage202.pullback
set_option pp.all true in
#check @ShielddSecurity.SubgroupPreimage202.eight_coordinates
#print axioms ShielddSecurity.SubgroupPreimage202.eight_coordinates
set_option pp.all true in
#check @ShielddSecurity.SubgroupPreimage202.member_preimage
#print axioms ShielddSecurity.SubgroupPreimage202.member_preimage
