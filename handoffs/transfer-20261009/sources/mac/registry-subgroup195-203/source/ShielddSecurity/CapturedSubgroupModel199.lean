import ShielddSecurity.TransferCore
import ShielddSecurity.GroupWindows
import ShielddSecurity.CompilerSubgroupClosure83
import ShielddSecurity.CapturedFourSubgroups82
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupModel199
open CompilerSubgroupArithmetic79
variable {F J : Type} [Field F] [AddCommGroup J]
def Member {d : F} (model : Group.StandardCurveModel J d) (point : Group.Point F) : Prop :=
 ∃ represented : J,model.coordinates represented=point ∧ TransferCore.scalarOrder • represented=0
theorem double_affine (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
 (valid : Group.OnCurve d point) : double d point=Group.affineAdd d point point := by
 have inverseRow : inverseProduct d point*(inverseProduct d point)⁻¹=1 :=
   mul_inv_cancel₀ (CompilerSubgroupClosure83.inverse_nonzero d imaginary nonSquare imaginarySquare point valid)
 exact (Group.shared_inverse_double_sound d imaginary (inverseProduct d point)⁻¹
   nonSquare imaginarySquare point (double d point) valid inverseRow rfl rfl).1
theorem trace_affine (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
 (valid : Group.OnCurve d point) (count : Nat) :
 trace d point (count+1)=Group.affineAdd d (trace d point count) (trace d point count) :=
 double_affine d imaginary nonSquare imaginarySquare _
   (CompilerSubgroupClosure83.trace_curve d imaginary nonSquare imaginarySquare point valid count)
theorem cofactor (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (model : Group.StandardCurveModel J d)
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0)
 (point : Group.Point F) (valid : Group.OnCurve d point) : Member model (eight d point) := by
 apply Group.cofactor_image_annihilated d model TransferCore.scalarOrder standardOrder point
   (trace d point 1) (trace d point 2) (eight d point) valid
 · exact trace_affine d imaginary nonSquare imaginarySquare point valid 0
 · exact trace_affine d imaginary nonSquare imaginarySquare point valid 1
 · exact trace_affine d imaginary nonSquare imaginarySquare point valid 2
variable [CharP F TransferFirstSubgroupData01.p]
theorem captured_four (rho : Nat → F) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0) :
 Member model ⟨rho 14,rho 15⟩ ∧ Member model ⟨rho 23,rho 24⟩ ∧
 Member model ⟨rho 35,rho 36⟩ ∧ Member model ⟨rho 42,rho 43⟩ := by
 rcases CapturedFourSubgroups82.all_four rho one satisfied with ⟨a,b,c,d⟩
 constructor
 · rw [←a.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ a.1
 constructor
 · rw [←b.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ b.1
 constructor
 · rw [←c.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ c.1
 · rw [←d.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ d.1
end ShielddSecurity.CapturedSubgroupModel199

set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupModel199.Member
#print axioms ShielddSecurity.CapturedSubgroupModel199.Member
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupModel199.double_affine
#print axioms ShielddSecurity.CapturedSubgroupModel199.double_affine
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupModel199.trace_affine
#print axioms ShielddSecurity.CapturedSubgroupModel199.trace_affine
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupModel199.cofactor
#print axioms ShielddSecurity.CapturedSubgroupModel199.cofactor
set_option pp.all true in
#check @ShielddSecurity.CapturedSubgroupModel199.captured_four
#print axioms ShielddSecurity.CapturedSubgroupModel199.captured_four
