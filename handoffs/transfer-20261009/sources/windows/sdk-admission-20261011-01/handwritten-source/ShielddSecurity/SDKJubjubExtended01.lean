import ShielddSecurity.GroupNativeMultiply

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKJubjubExtended01

/-- Source model of jubjub0.10.0's five-coordinate ExtendedPoint. The
field operations are mathematical; a native field representation refinement
is still required to instantiate this model with Rust values. -/
structure Extended (F : Type) where
  u : F
  v : F
  z : F
  t1 : F
  t2 : F

structure Niels (F : Type) where
  vPlusU : F
  vMinusU : F
  z : F
  t2d : F

variable {F : Type} [Field F]

def collapse (value : Extended F) : GroupExtended.Extended F :=
  ⟨value.u, value.v, value.z, value.t1 * value.t2⟩

def affine (point : Group.Point F) : Extended F :=
  ⟨point.x, point.y, 1, point.x, point.y⟩

/-- CompletedPoint::into_extended in native assignment order. -/
def finish (u v z t : F) : Extended F := ⟨u * t, v * z, z * t, u, v⟩

def toNiels (d : F) (value : Extended F) : Niels F :=
  ⟨value.v + value.u, value.v - value.u, value.z, value.t1 * value.t2 * (d + d)⟩

def addNiels (left : Extended F) (right : Niels F) : Extended F :=
  let a := (left.v - left.u) * right.vMinusU
  let b := (left.v + left.u) * right.vPlusU
  let c := left.t1 * left.t2 * right.t2d
  let dd := left.z * right.z + left.z * right.z
  finish (b - a) (b + a) (dd + c) (dd - c)

def add (d : F) (left right : Extended F) : Extended F := addNiels left (toNiels d right)

/-- Exact signs of SDK double(): J=2Z²-(V²-U²). The owned native
double uses the opposite projective scale, so coordinate equality is not
asserted between their internal representations. -/
def double (value : Extended F) : Extended F :=
  let uu := value.u * value.u
  let vv := value.v * value.v
  let zz2 := value.z * value.z + value.z * value.z
  let uv2 := (value.u + value.v) * (value.u + value.v)
  let plus := vv + uu
  let minus := vv - uu
  finish (uv2 - plus) plus minus (zz2 - minus)

def negAll (value : GroupExtended.Extended F) : GroupExtended.Extended F :=
  ⟨-value.x, -value.y, -value.z, -value.t⟩

def Represents (value : Extended F) (point : Group.Point F) : Prop :=
  GroupExtended.Represents (collapse value) point

def normalize (value : Extended F) : Group.Point F :=
  ⟨value.u * value.z⁻¹, value.v * value.z⁻¹⟩

def isIdentity (value : Extended F) : Prop := value.u = 0 ∧ value.v = value.z

theorem collapse_affine (point : Group.Point F) :
    collapse (affine point) = GroupExtended.affine point := rfl

theorem collapse_finish (u v z t : F) :
    collapse (finish u v z t) = GroupExtended.finish u t z v := by
  dsimp [collapse, finish, GroupExtended.finish]
  congr 1 <;> ring

theorem collapse_add (d : F) (left right : Extended F) :
    collapse (add d left right) = GroupExtended.add d (collapse left) (collapse right) := by
  dsimp [collapse, add, addNiels, toNiels, finish,
    GroupExtended.add, GroupExtended.finish]
  congr 1 <;> ring

theorem collapse_double (value : Extended F) :
    collapse (double value) = negAll (GroupExtended.double (collapse value)) := by
  dsimp [collapse, double, finish, negAll,
    GroupExtended.double, GroupExtended.finish]
  congr 1 <;> ring

theorem neg_all_represents (value : GroupExtended.Extended F) (point : Group.Point F)
    (represented : GroupExtended.Represents value point) :
    GroupExtended.Represents (negAll value) point := by
  refine ⟨neg_ne_zero.mpr represented.1, ?_, ?_, ?_⟩
  · change -value.x = point.x * -value.z
    rw [represented.2.1]
    ring
  · change -value.y = point.y * -value.z
    rw [represented.2.2.1]
    ring
  · change -value.t = point.x * point.y * -value.z
    rw [represented.2.2.2]
    ring

theorem affine_represents (point : Group.Point F) : Represents (affine point) point := by
  unfold Represents
  rw [collapse_affine]
  exact GroupExtended.affine_represents point

theorem normalize_represents (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) : normalize value = point :=
  GroupExtended.normalize_represents (collapse value) point represented

theorem double_represents (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) (valid : Group.OnCurve d point) :
    Represents (double value) (Group.affineAdd d point point) := by
  unfold Represents
  rw [collapse_double]
  exact neg_all_represents _ _
    (GroupExtended.double_represents d imaginary nonSquare imaginarySquare
      (collapse value) point represented valid).1

theorem add_represents (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (left right : Extended F) (p q : Group.Point F)
    (leftRep : Represents left p) (rightRep : Represents right q)
    (pValid : Group.OnCurve d p) (qValid : Group.OnCurve d q) :
    Represents (add d left right) (Group.affineAdd d p q) := by
  unfold Represents
  rw [collapse_add]
  exact GroupExtended.add_represents d imaginary nonSquare imaginarySquare two
    (collapse left) (collapse right) p q leftRep rightRep pValid qValid

/-- SDK identity testing reflects the represented affine identity; nonzero Z
is supplied by the representation invariant, not by a desired test result. -/
theorem identity_test_iff (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) : isIdentity value ↔ point = Group.identityPoint := by
  constructor
  · intro tested
    have xZero : point.x = 0 := by
      have row := represented.2.1
      change value.u = point.x * value.z at row
      rw [tested.1] at row
      exact (mul_eq_zero.mp row.symm).resolve_right represented.1
    have yOne : point.y = 1 := by
      have row := represented.2.2.1
      change value.v = point.y * value.z at row
      rw [tested.2] at row
      exact (mul_right_cancel₀ represented.1 (by simpa only [one_mul] using row.symm))
    cases point
    exact congrArg₂ Group.Point.mk xZero yOne
  · intro equal
    subst point
    exact ⟨by simpa only [Group.identityPoint, zero_mul] using represented.2.1,
      by simpa only [Group.identityPoint, one_mul] using represented.2.2.1⟩


end ShielddSecurity.SDKJubjubExtended01

set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.Extended
#print axioms ShielddSecurity.SDKJubjubExtended01.Extended
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.Niels
#print axioms ShielddSecurity.SDKJubjubExtended01.Niels
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.collapse
#print axioms ShielddSecurity.SDKJubjubExtended01.collapse
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.affine
#print axioms ShielddSecurity.SDKJubjubExtended01.affine
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.finish
#print axioms ShielddSecurity.SDKJubjubExtended01.finish
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.toNiels
#print axioms ShielddSecurity.SDKJubjubExtended01.toNiels
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.addNiels
#print axioms ShielddSecurity.SDKJubjubExtended01.addNiels
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.add
#print axioms ShielddSecurity.SDKJubjubExtended01.add
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.double
#print axioms ShielddSecurity.SDKJubjubExtended01.double
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.negAll
#print axioms ShielddSecurity.SDKJubjubExtended01.negAll
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.Represents
#print axioms ShielddSecurity.SDKJubjubExtended01.Represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.normalize
#print axioms ShielddSecurity.SDKJubjubExtended01.normalize
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.isIdentity
#print axioms ShielddSecurity.SDKJubjubExtended01.isIdentity
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.collapse_affine
#print axioms ShielddSecurity.SDKJubjubExtended01.collapse_affine
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.collapse_finish
#print axioms ShielddSecurity.SDKJubjubExtended01.collapse_finish
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.collapse_add
#print axioms ShielddSecurity.SDKJubjubExtended01.collapse_add
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.collapse_double
#print axioms ShielddSecurity.SDKJubjubExtended01.collapse_double
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.neg_all_represents
#print axioms ShielddSecurity.SDKJubjubExtended01.neg_all_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.affine_represents
#print axioms ShielddSecurity.SDKJubjubExtended01.affine_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.normalize_represents
#print axioms ShielddSecurity.SDKJubjubExtended01.normalize_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.double_represents
#print axioms ShielddSecurity.SDKJubjubExtended01.double_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.add_represents
#print axioms ShielddSecurity.SDKJubjubExtended01.add_represents
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubExtended01.identity_test_iff
#print axioms ShielddSecurity.SDKJubjubExtended01.identity_test_iff
