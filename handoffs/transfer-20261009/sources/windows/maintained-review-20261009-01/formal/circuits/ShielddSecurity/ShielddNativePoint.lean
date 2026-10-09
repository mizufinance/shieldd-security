import ShielddSecurity.ShielddNativeScalar
import ShielddSecurity.GroupNativeMultiply

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativePoint

variable {F Raw : Type} [Field F]

/-- Coordinates contain the owned Scalar wrapper. Raw denotes the valid
reachable BLST states in ShielddNativeScalar.Operations, so these definitions
use only its named global primitive contracts. -/
structure Point (Raw : Type) where
  x : ShielddNativeScalar.Wrapped Raw
  y : ShielddNativeScalar.Wrapped Raw

structure Extended (Raw : Type) where
  x : ShielddNativeScalar.Wrapped Raw
  y : ShielddNativeScalar.Wrapped Raw
  z : ShielddNativeScalar.Wrapped Raw
  t : ShielddNativeScalar.Wrapped Raw

def pointValue (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Point Raw) : Group.Point F :=
  ⟨ShielddNativeScalar.value operations point.x, ShielddNativeScalar.value operations point.y⟩

def extendedValue (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Extended Raw) : GroupExtended.Extended F :=
  ⟨ShielddNativeScalar.value operations point.x, ShielddNativeScalar.value operations point.y,
    ShielddNativeScalar.value operations point.z, ShielddNativeScalar.value operations point.t⟩

def identity (operations : ShielddNativeScalar.Operations (F := F) Raw) : Point Raw :=
  ⟨ShielddNativeScalar.zero operations, ShielddNativeScalar.one operations⟩

/-- group.rs Point::add, including its one shared inverse and the native
xx*yy*d multiplication order. This is not the optimized circuit window add. -/
def pointAdd (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (left right : Point Raw) : Point Raw :=
  let add := ShielddNativeScalar.add operations
  let sub := ShielddNativeScalar.sub operations
  let mul := ShielddNativeScalar.mul operations
  let xx := mul left.x right.x
  let yy := mul left.y right.y
  let dt := mul (mul xx yy) d
  let plus := add (ShielddNativeScalar.one operations) dt
  let minus := sub (ShielddNativeScalar.one operations) dt
  let inverse := ShielddNativeScalar.inverse operations (mul plus minus)
  ⟨mul (mul (add (mul left.x right.y) (mul left.y right.x)) minus) inverse,
    mul (mul (add yy xx) plus) inverse⟩

def affine (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Point Raw) : Extended Raw :=
  ⟨point.x,point.y,ShielddNativeScalar.one operations,
    ShielddNativeScalar.mul operations point.x point.y⟩

def finish (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (e f g h : ShielddNativeScalar.Wrapped Raw) : Extended Raw :=
  ⟨ShielddNativeScalar.mul operations e f, ShielddNativeScalar.mul operations g h,
    ShielddNativeScalar.mul operations f g, ShielddNativeScalar.mul operations e h⟩

def extendedAdd (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (left right : Extended Raw) : Extended Raw :=
  let add := ShielddNativeScalar.add operations
  let sub := ShielddNativeScalar.sub operations
  let mul := ShielddNativeScalar.mul operations
  let a := mul (sub left.y left.x) (sub right.y right.x)
  let b := mul (add left.y left.x) (add right.y right.x)
  let c := mul (mul left.t right.t) (add d d)
  let dd := mul left.z (add right.z right.z)
  finish operations (sub b a) (sub dd c) (add dd c) (add b a)

def extendedDouble (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Extended Raw) : Extended Raw :=
  let add := ShielddNativeScalar.add operations
  let sub := ShielddNativeScalar.sub operations
  let mul := ShielddNativeScalar.mul operations
  let a := mul point.x point.x
  let b := mul point.y point.y
  let zz := mul point.z point.z
  let c := add zz zz
  let d := ShielddNativeScalar.neg operations a
  let sum := add point.x point.y
  let e := sub (sub (mul sum sum) a) b
  let g := add d b
  finish operations e (sub g c) g (sub d b)

def normalize (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Extended Raw) : Point Raw :=
  let inverse := ShielddNativeScalar.inverse operations point.z
  ⟨ShielddNativeScalar.mul operations point.x inverse,
    ShielddNativeScalar.mul operations point.y inverse⟩

/-- Native multiply uses field arithmetic for selection. Boolean meaning is
established only when its bit is the owned zero/one constructed from Bool. -/
def choose (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bit yes no : ShielddNativeScalar.Wrapped Raw) : ShielddNativeScalar.Wrapped Raw :=
  ShielddNativeScalar.add operations no (ShielddNativeScalar.mul operations bit
    (ShielddNativeScalar.sub operations yes no))

def boolean (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bit : Bool) : ShielddNativeScalar.Wrapped Raw :=
  if bit then ShielddNativeScalar.one operations else ShielddNativeScalar.zero operations

theorem identity_value (operations : ShielddNativeScalar.Operations (F := F) Raw) :
    pointValue operations (identity operations) = Group.identityPoint := by
  simp only [pointValue, identity, Group.identityPoint,
    ShielddNativeScalar.zero_value, ShielddNativeScalar.one_value]

theorem point_add_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (left right : Point Raw) :
    pointValue operations (pointAdd operations d left right) =
      GroupFixedWindows.nativeAdd (ShielddNativeScalar.value operations d)
        (pointValue operations left) (pointValue operations right) := by
  have delta :
      (ShielddNativeScalar.value operations left.x * ShielddNativeScalar.value operations right.x) *
      (ShielddNativeScalar.value operations left.y * ShielddNativeScalar.value operations right.y) *
      ShielddNativeScalar.value operations d =
        Group.delta (ShielddNativeScalar.value operations d)
          (pointValue operations left) (pointValue operations right) := by
    simp only [Group.delta,pointValue]
    ring
  simp only [pointAdd,pointValue,ShielddNativeScalar.add_value,
    ShielddNativeScalar.sub_value,ShielddNativeScalar.mul_value,
    ShielddNativeScalar.one_value,ShielddNativeScalar.inverse_value]
  rw [delta]
  rfl

theorem affine_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Point Raw) : extendedValue operations (affine operations point) =
      GroupExtended.affine (pointValue operations point) := by
  simp only [affine,extendedValue,pointValue,GroupExtended.affine,
    ShielddNativeScalar.one_value,ShielddNativeScalar.mul_value]

theorem extended_add_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (left right : Extended Raw) :
    extendedValue operations (extendedAdd operations d left right) =
      GroupExtended.add (ShielddNativeScalar.value operations d)
        (extendedValue operations left) (extendedValue operations right) := by
  simp only [extendedAdd,finish,extendedValue,GroupExtended.add,GroupExtended.finish,
    ShielddNativeScalar.add_value,ShielddNativeScalar.sub_value,ShielddNativeScalar.mul_value]

theorem extended_double_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Extended Raw) : extendedValue operations (extendedDouble operations point) =
      GroupExtended.double (extendedValue operations point) := by
  simp only [extendedDouble,finish,extendedValue,GroupExtended.double,GroupExtended.finish,
    ShielddNativeScalar.add_value,ShielddNativeScalar.sub_value,
    ShielddNativeScalar.mul_value,ShielddNativeScalar.neg_value]

theorem normalize_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (point : Extended Raw) : pointValue operations (normalize operations point) =
      GroupExtended.normalize (extendedValue operations point) := by
  simp only [normalize,pointValue,extendedValue,GroupExtended.normalize,
    ShielddNativeScalar.mul_value,ShielddNativeScalar.inverse_value]

theorem choose_boolean_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bit : Bool) (yes no : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativeScalar.value operations (choose operations (boolean operations bit) yes no) =
      if bit then ShielddNativeScalar.value operations yes else ShielddNativeScalar.value operations no := by
  cases bit <;> simp [choose,boolean,ShielddNativeScalar.add_value,
    ShielddNativeScalar.sub_value,ShielddNativeScalar.mul_value,
    ShielddNativeScalar.zero_value,ShielddNativeScalar.one_value]

set_option pp.all true in
#check @identity_value
#print axioms identity_value
set_option pp.all true in
#check @point_add_value
#print axioms point_add_value
set_option pp.all true in
#check @affine_value
#print axioms affine_value
set_option pp.all true in
#check @extended_add_value
#print axioms extended_add_value
set_option pp.all true in
#check @extended_double_value
#print axioms extended_double_value
set_option pp.all true in
#check @normalize_value
#print axioms normalize_value
set_option pp.all true in
#check @choose_boolean_value
#print axioms choose_boolean_value

end ShielddSecurity.ShielddNativePoint
