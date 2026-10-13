import ShielddSecurity.CapturedAuthorizationAdd509
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationAddRows511
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]

theorem coordinates (d : F) (left right : Group.Point F)
    (nonzero : (1+Group.delta d left right)*(1-Group.delta d left right)≠0) :
    Group.Point.mk
      (Group.cross left right*(1-Group.delta d left right)*((1+Group.delta d left right)*(1-Group.delta d left right))⁻¹)
      (Group.diagonal left right*(1+Group.delta d left right)*((1+Group.delta d left right)*(1-Group.delta d left right))⁻¹)=
    Group.affineAdd d left right := by
  have parts := mul_ne_zero_iff.mp nonzero
  apply congrArg₂ Group.Point.mk
  · change _=Group.cross left right/(1+Group.delta d left right)
    field_simp [parts.1,parts.2]
  · change _=Group.diagonal left right/(1-Group.delta d left right)
    field_simp [parts.1,parts.2]

theorem complete (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (left right output : Group.Point F)
    (leftMeaning : VariableWindowColumns449.columnPoint rho 1980=left)
    (rightMeaning : VariableWindowColumns449.columnPoint rho 4269=right)
    (outputMeaning : VariableWindowColumns449.columnPoint rho 4272=output)
    (inverseMeaning : rho 4271=((1+Group.delta (CapturedFirstSubgroup81.d:F) left right)*
      (1-Group.delta (CapturedFirstSubgroup81.d:F) left right))⁻¹)
    (nonzero : (1+Group.delta (CapturedFirstSubgroup81.d:F) left right)*(1-Group.delta (CapturedFirstSubgroup81.d:F) left right)≠0)
    (result : output=Group.affineAdd (CapturedFirstSubgroup81.d:F) left right) :
    CapturedAuthorizationAdd509.Rows rho := by
  have values := CapturedAuthorizationAdd509.values rho one arithmetic
  dsimp only at values
  rw [leftMeaning,rightMeaning,inverseMeaning] at values
  apply (CapturedAuthorizationAdd509.rows_iff rho one).mpr
  refine ⟨values.1.trans (inv_mul_cancel₀ nonzero),?_,?_⟩
  · have point := (congrArg₂ Group.Point.mk values.2.1 values.2.2).trans
      ((coordinates (CapturedFirstSubgroup81.d:F) left right nonzero).trans (result.symm.trans outputMeaning.symm))
    exact congrArg Group.Point.x point
  · have point := (congrArg₂ Group.Point.mk values.2.1 values.2.2).trans
      ((coordinates (CapturedFirstSubgroup81.d:F) left right nonzero).trans (result.symm.trans outputMeaning.symm))
    exact congrArg Group.Point.y point
end ShielddSecurity.AuthorizationAddRows511
set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddRows511.coordinates
#print axioms ShielddSecurity.AuthorizationAddRows511.coordinates
set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddRows511.complete
#print axioms ShielddSecurity.AuthorizationAddRows511.complete
