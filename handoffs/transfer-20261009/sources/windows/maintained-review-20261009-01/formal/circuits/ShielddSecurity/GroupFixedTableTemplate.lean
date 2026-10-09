import ShielddSecurity.GroupFixedWindowTemplate
import ShielddSecurity.GroupFixedWindows

set_option maxHeartbeats 250000
set_option maxRecDepth 4096

namespace ShielddSecurity.GroupFixedTableTemplate

structure AdditionData where
  left : Group.Point Int
  right : Group.Point Int
  output : Group.Point Int

def xCertificate (p : Nat) (d : Int) (data : AdditionData) : Prop :=
  Compiler.canonical p [(0,data.output.x *
    (1+d*data.left.x*data.right.x*data.left.y*data.right.y))] =
  Compiler.canonical p [(0,data.left.x*data.right.y+data.left.y*data.right.x)]

def yCertificate (p : Nat) (d : Int) (data : AdditionData) : Prop :=
  Compiler.canonical p [(0,data.output.y *
    (1-d*data.left.x*data.right.x*data.left.y*data.right.y))] =
  Compiler.canonical p [(0,data.left.y*data.right.y+data.left.x*data.right.x)]

variable {F : Type} [Field F]

/-- Finite actual native table coefficients entail the exact owned shared
inverse Point::add result, using the independent complete-curve contracts.
Neither a native output-coordinate equality nor division legality is assumed. -/
theorem checked_add {p : Nat} [CharP F p] (d : Int) (data : AdditionData)
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (leftValid : Group.OnCurve (d : F) (GroupFixedWindowTemplate.castPoint data.left))
    (rightValid : Group.OnCurve (d : F) (GroupFixedWindowTemplate.castPoint data.right))
    (checkedX : xCertificate p d data) (checkedY : yCertificate p d data) :
    GroupFixedWindowTemplate.castPoint data.output = GroupFixedWindows.nativeAdd (d : F)
      (GroupFixedWindowTemplate.castPoint data.left) (GroupFixedWindowTemplate.castPoint data.right) := by
  have xRow := Compiler.canonical_equal rho
    [(0,data.output.x*(1+d*data.left.x*data.right.x*data.left.y*data.right.y))]
    [(0,data.left.x*data.right.y+data.left.y*data.right.x)] checkedX
  have yRow := Compiler.canonical_equal rho
    [(0,data.output.y*(1-d*data.left.x*data.right.x*data.left.y*data.right.y))]
    [(0,data.left.y*data.right.y+data.left.x*data.right.x)] checkedY
  simp only [eval,one,mul_one,add_zero,Int.cast_mul,Int.cast_add,Int.cast_sub,Int.cast_one] at xRow yRow
  have affine := Group.affine_rows_sound (d : F) imaginary nonSquare imaginarySquare
    (GroupFixedWindowTemplate.castPoint data.left) (GroupFixedWindowTemplate.castPoint data.right)
    (GroupFixedWindowTemplate.castPoint data.output) leftValid rightValid xRow yRow
  exact affine.trans (GroupFixedWindows.native_add_affine (d : F) imaginary nonSquare imaginarySquare
    _ _ leftValid rightValid).symm

/-- Reuse the symbolic standard-curve weighted table theorem. All three native
operations come from finite constant certificates, and the initial represented
base is a global/source parameter interpretation, not a scalar-output premise. -/
theorem weighted_table {p : Nat} [CharP F p] {J : Type} [AddCommGroup J]
    (d : Int) (model : Group.StandardCurveModel J (d : F)) (represented : J)
    (base twice triple nextBase : Group.Point Int) (rho : Nat → F) (one : rho 0 = 1)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (sourceBase : GroupFixedWindowTemplate.castPoint base = model.coordinates represented)
    (baseValid : Group.OnCurve (d : F) (GroupFixedWindowTemplate.castPoint base))
    (twiceValid : Group.OnCurve (d : F) (GroupFixedWindowTemplate.castPoint twice))
    (checkedX2 : xCertificate p d ⟨base,base,twice⟩)
    (checkedY2 : yCertificate p d ⟨base,base,twice⟩)
    (checkedX3 : xCertificate p d ⟨twice,base,triple⟩)
    (checkedY3 : yCertificate p d ⟨twice,base,triple⟩)
    (checkedX4 : xCertificate p d ⟨twice,twice,nextBase⟩)
    (checkedY4 : yCertificate p d ⟨twice,twice,nextBase⟩) :
    GroupFixedWindowTemplate.castPoint twice = model.coordinates (2 • represented) ∧
    GroupFixedWindowTemplate.castPoint triple = model.coordinates (3 • represented) ∧
    GroupFixedWindowTemplate.castPoint nextBase = model.coordinates (4 • represented) := by
  let window : GroupFixedWindows.FixedWindowWitness F :=
    ⟨false,false,GroupFixedWindowTemplate.castPoint twice,GroupFixedWindowTemplate.castPoint triple,
      GroupFixedWindowTemplate.castPoint nextBase,Group.identityPoint⟩
  have first := checked_add d ⟨base,base,twice⟩ rho one imaginary nonSquare imaginarySquare
    baseValid baseValid checkedX2 checkedY2
  have second := checked_add d ⟨twice,base,triple⟩ rho one imaginary nonSquare imaginarySquare
    twiceValid baseValid checkedX3 checkedY3
  have third := checked_add d ⟨twice,twice,nextBase⟩ rho one imaginary nonSquare imaginarySquare
    twiceValid twiceValid checkedX4 checkedY4
  have equations : GroupFixedWindows.FixedTableEquations (d : F) (model.coordinates represented) window := by
    change GroupFixedWindowTemplate.castPoint twice = _ ∧
      GroupFixedWindowTemplate.castPoint triple = _ ∧ GroupFixedWindowTemplate.castPoint nextBase = _
    rw [sourceBase] at first second
    exact ⟨first,second,third⟩
  exact GroupFixedWindows.fixed_table_coordinates (d : F) imaginary model nonSquare imaginarySquare
    represented window equations

set_option pp.all true in
#check @checked_add
#print axioms checked_add
set_option pp.all true in
#check @weighted_table
#print axioms weighted_table

end ShielddSecurity.GroupFixedTableTemplate
