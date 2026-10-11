import ShielddSecurity.GroupNativeCofactor
import ShielddSecurity.GroupNativeNonidentity

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupNativeSubgroupWitness

variable {F : Type} [Field F]

/-- Exact shared-product inverse used by Point::add and hence the three
existing witness_subgroup doublings. These are source witness values; original
compiler square/product/assertion rows require independent shape transport. -/
def sharedInverse (d : F) (point : Group.Point F) : F :=
  ((1 + Group.delta d point point) * (1 - Group.delta d point point))⁻¹

def DoubleConstraints (d : F) (point : Group.Point F) : Prop :=
  ((1 + Group.delta d point point) * (1 - Group.delta d point point)) *
      sharedInverse d point = 1 ∧
    (GroupFixedWindows.nativeAdd d point point).x =
      Group.cross point point * (1 - Group.delta d point point) * sharedInverse d point ∧
    (GroupFixedWindows.nativeAdd d point point).y =
      Group.diagonal point point * (1 + Group.delta d point point) * sharedInverse d point

theorem native_double_constraints (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (point : Group.Point F)
    (valid : Group.OnCurve d point) : DoubleConstraints d point := by
  have denominators := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    point point valid valid
  exact ⟨mul_inv_cancel₀ (mul_ne_zero denominators.1 denominators.2),rfl,rfl⟩

/-- Construct all six native witness values required by the fresh RK observer:
preimage x/y, the shared inverse at each of three doublings, and the public x
inverse. Each retained assertion is an arithmetic conclusion from independently
admitted subgroup/nonidentity input plus global codec/full-group contracts.
No desired preimage, inverse equation, output subgroup or Satisfies is assumed.
The actual source/LC allocation and original-row completeness remain mandatory. -/
theorem native_subgroup_constraints [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (point : J) (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0) :
    let preimage := GroupNativeCofactor.nativePreimage d codec writer (model.coordinates point)
    let twice := GroupFixedWindows.nativeAdd d preimage preimage
    let four := GroupFixedWindows.nativeAdd d twice twice
    Group.OnCurve d preimage ∧
      DoubleConstraints d preimage ∧ DoubleConstraints d twice ∧ DoubleConstraints d four ∧
      GroupNativeCofactor.nativeEight d preimage = model.coordinates point ∧
      (model.coordinates point).x * ((model.coordinates point).x)⁻¹ = 1 := by
  dsimp only
  let preimage := GroupNativeCofactor.nativePreimage d codec writer (model.coordinates point)
  let twice := GroupFixedWindows.nativeAdd d preimage preimage
  let four := GroupFixedWindows.nativeAdd d twice twice
  have preimageCoordinates : preimage = model.coordinates (GroupNativeCofactor.inverseEight • point) :=
    GroupNativeCofactor.native_preimage_coordinates codec writer d imaginary model nonSquare
      imaginarySquare two point
  have twiceCoordinates : twice = model.coordinates
      ((GroupNativeCofactor.inverseEight • point) + (GroupNativeCofactor.inverseEight • point)) := by
    dsimp only [twice]
    rw [preimageCoordinates]
    exact GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare _ _
  have fourCoordinates : four = model.coordinates
      (((GroupNativeCofactor.inverseEight • point) + (GroupNativeCofactor.inverseEight • point)) +
        ((GroupNativeCofactor.inverseEight • point) + (GroupNativeCofactor.inverseEight • point))) := by
    dsimp only [four]
    rw [twiceCoordinates]
    exact GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare _ _
  have preimageValid : Group.OnCurve d preimage := by rw [preimageCoordinates]; exact model.onCurve _
  have twiceValid : Group.OnCurve d twice := by rw [twiceCoordinates]; exact model.onCurve _
  have fourValid : Group.OnCurve d four := by rw [fourCoordinates]; exact model.onCurve _
  exact ⟨preimageValid,
    native_double_constraints d imaginary nonSquare imaginarySquare preimage preimageValid,
    native_double_constraints d imaginary nonSquare imaginarySquare twice twiceValid,
    native_double_constraints d imaginary nonSquare imaginarySquare four fourValid,
    (GroupNativeCofactor.native_preimage_complete codec writer d imaginary model nonSquare
      imaginarySquare two point subgroup).2,
    GroupNativeNonidentity.nonidentity_inverse_coordinates d model point subgroup nonidentity⟩

set_option pp.all true in
#check @native_double_constraints
#print axioms native_double_constraints
set_option pp.all true in
#check @native_subgroup_constraints
#print axioms native_subgroup_constraints

end ShielddSecurity.GroupNativeSubgroupWitness
