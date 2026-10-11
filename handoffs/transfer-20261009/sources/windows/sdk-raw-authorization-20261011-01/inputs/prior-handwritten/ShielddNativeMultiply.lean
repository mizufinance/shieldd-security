import ShielddSecurity.ShielddNativePoint

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeMultiply

variable {F Raw : Type} [Field F]

/-- group.rs converts each unsigned byte bit with Scalar::from(u64).
No arbitrary raw Scalar is assumed to have Boolean meaning. -/
def bitScalar (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (bit : Bool) : ShielddNativeScalar.Wrapped Raw :=
  ShielddNativeScalar.fromU64 operations bit.toNat

theorem bit_value (operations : ShielddNativeScalar.Operations (F := F) Raw) (bit : Bool) :
    ShielddNativeScalar.value operations (bitScalar operations bit) = if bit then 1 else 0 := by
  cases bit with
  | false =>
      change ShielddNativeScalar.value operations (ShielddNativeScalar.fromU64 operations 0) = 0
      simpa only [Nat.cast_zero] using
        ShielddNativeScalar.from_u64_value operations 0 (by decide)
  | true =>
      change ShielddNativeScalar.value operations (ShielddNativeScalar.fromU64 operations 1) = 1
      simpa only [Nat.cast_one] using
        ShielddNativeScalar.from_u64_value operations 1 (by decide)

def window (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (base twice triple : ShielddNativePoint.Point Raw) (pair : Bool × Bool) :
    ShielddNativePoint.Point Raw :=
  let choose := ShielddNativePoint.choose operations
  let low := bitScalar operations pair.1
  let high := bitScalar operations pair.2
  ⟨choose high (choose low triple.x twice.x)
      (choose low base.x (ShielddNativeScalar.zero operations)),
    choose high (choose low triple.y twice.y)
      (choose low base.y (ShielddNativeScalar.one operations))⟩

theorem window_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (base twice triple : ShielddNativePoint.Point Raw) (pair : Bool × Bool) :
    ShielddNativePoint.pointValue operations (window operations base twice triple pair) =
      Group.windowPoint (if pair.1 then 1 else 0) (if pair.2 then 1 else 0)
        (ShielddNativePoint.pointValue operations base)
        (ShielddNativePoint.pointValue operations twice)
        (ShielddNativePoint.pointValue operations triple) := by
  simp only [window,ShielddNativePoint.pointValue,ShielddNativePoint.choose,
    ShielddNativeScalar.add_value,ShielddNativeScalar.sub_value,ShielddNativeScalar.mul_value,
    ShielddNativeScalar.zero_value,ShielddNativeScalar.one_value,bit_value,
    Group.windowPoint,Group.chooseCoordinate]

def step (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (base twice triple : ShielddNativePoint.Point Raw)
    (result : ShielddNativePoint.Extended Raw) (pair : Bool × Bool) :
    ShielddNativePoint.Extended Raw :=
  ShielddNativePoint.extendedAdd operations d
    (ShielddNativePoint.extendedDouble operations (ShielddNativePoint.extendedDouble operations result))
    (ShielddNativePoint.affine operations (window operations base twice triple pair))

theorem step_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (base twice triple : ShielddNativePoint.Point Raw)
    (result : ShielddNativePoint.Extended Raw) (pair : Bool × Bool) :
    ShielddNativePoint.extendedValue operations (step operations d base twice triple result pair) =
      GroupNativeMultiply.nativeStep (ShielddNativeScalar.value operations d)
        (ShielddNativePoint.pointValue operations base)
        (ShielddNativePoint.pointValue operations twice)
        (ShielddNativePoint.pointValue operations triple)
        (ShielddNativePoint.extendedValue operations result) pair := by
  simp only [step,GroupNativeMultiply.nativeStep,ShielddNativePoint.extended_add_value,
    ShielddNativePoint.extended_double_value,ShielddNativePoint.affine_value,window_value]

/-- The chunk pairs and their reversed traversal come from the actual bit
list. pairBits has already proved the odd high=false and digit-order laws.
The source's odd-chunk F::zero and from(0) have equal interpreted values. -/
def multiplyExtended (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (base : ShielddNativePoint.Point Raw)
    (bits : List Bool) : ShielddNativePoint.Extended Raw :=
  let twice := ShielddNativePoint.pointAdd operations d base base
  let triple := ShielddNativePoint.pointAdd operations d twice base
  (GroupNativeMultiply.pairBits bits).reverse.foldl (step operations d base twice triple)
    (ShielddNativePoint.affine operations (ShielddNativePoint.identity operations))

def multiply (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (base : ShielddNativePoint.Point Raw)
    (bits : List Bool) : ShielddNativePoint.Point Raw :=
  ShielddNativePoint.normalize operations (multiplyExtended operations d base bits)

theorem fold_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (base twice triple : ShielddNativePoint.Point Raw)
    (pairs : List (Bool × Bool)) (result : ShielddNativePoint.Extended Raw) :
    ShielddNativePoint.extendedValue operations
        (pairs.foldl (step operations d base twice triple) result) =
      pairs.foldl (GroupNativeMultiply.nativeStep (ShielddNativeScalar.value operations d)
        (ShielddNativePoint.pointValue operations base)
        (ShielddNativePoint.pointValue operations twice)
        (ShielddNativePoint.pointValue operations triple))
        (ShielddNativePoint.extendedValue operations result) := by
  induction pairs generalizing result with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.foldl_cons]
      rw [ih,step_value]

theorem multiply_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (base : ShielddNativePoint.Point Raw) (bits : List Bool) :
    ShielddNativePoint.pointValue operations (multiply operations d base bits) =
      GroupNativeMultiply.nativeMultiply (ShielddNativeScalar.value operations d)
        (ShielddNativePoint.pointValue operations base) bits := by
  simp only [multiply,ShielddNativePoint.normalize_value,multiplyExtended,
    GroupNativeMultiply.nativeMultiply,GroupNativeMultiply.multiplyExtended,fold_value,
    ShielddNativePoint.point_add_value,ShielddNativePoint.affine_value,ShielddNativePoint.identity_value]

theorem multiply_coordinates {J : Type} [AddCommGroup J]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (d : ShielddNativeScalar.Wrapped Raw) (imaginary : F)
    (model : Group.StandardCurveModel J (ShielddNativeScalar.value operations d))
    (nonSquare : Group.NoUnitSquare (ShielddNativeScalar.value operations d))
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : ShielddNativePoint.Point Raw) (point : J)
    (input : ShielddNativePoint.pointValue operations base = model.coordinates point)
    (bits : List Bool) :
    ShielddNativePoint.pointValue operations (multiply operations d base bits) =
      model.coordinates (ShielddSecurity.binary bits • point) := by
  rw [multiply_value,input]
  exact GroupNativeMultiply.native_multiply_coordinates _ imaginary model nonSquare imaginarySquare two point bits

set_option pp.all true in
#check @bit_value
#print axioms bit_value
set_option pp.all true in
#check @window_value
#print axioms window_value
set_option pp.all true in
#check @step_value
#print axioms step_value
set_option pp.all true in
#check @fold_value
#print axioms fold_value
set_option pp.all true in
#check @multiply_value
#print axioms multiply_value
set_option pp.all true in
#check @multiply_coordinates
#print axioms multiply_coordinates

end ShielddSecurity.ShielddNativeMultiply
