import ShielddSecurity.ShielddNativeSdk
import ShielddSecurity.ElligatorNativeRootInterop
import ShielddSecurity.ElligatorCurve

set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace ShielddSecurity.NativeAssetMap

variable {F Q : Type} [Field F] [DecidableEq F]

def value (fq : GroupNativeSdk.FqBytes Q) (q : Q) : F := (fq.integer q : F)

/-- Named upstream Fq primitives, interpreted globally. There is no whole
Shieldd map function or chosen input/output point in this contract. `invert`
is the native Option operation, including its zero case. -/
structure Primitives (fq : GroupNativeSdk.FqBytes Q)
    (api : ElligatorNativeRoots.SqrtAPI F) where
  zero : Q
  natural : Nat → Q
  add : Q → Q → Q
  mul : Q → Q → Q
  neg : Q → Q
  invert : Q → Option Q
  sqrt : Q → Option Q
  zeroValue : value (F := F) fq zero = 0
  naturalValue : ∀ n, n < 2^64 → value (F := F) fq (natural n) = (n : F)
  addValue : ∀ a b, value (F := F) fq (add a b) = value (F := F) fq a + value (F := F) fq b
  mulValue : ∀ a b, value (F := F) fq (mul a b) = value (F := F) fq a * value (F := F) fq b
  negValue : ∀ a, value (F := F) fq (neg a) = -value (F := F) fq a
  invertValue : ∀ a, (invert a).map (value (F := F) fq) =
    if value (F := F) fq a = 0 then none else some ((value (F := F) fq a)⁻¹)
  sqrtValue : ∀ a, (sqrt a).map (value (F := F) fq) = api.sqrt (value (F := F) fq a)

variable (fq : GroupNativeSdk.FqBytes Q) (api : ElligatorNativeRoots.SqrtAPI F)
variable (ops : Primitives fq api)

private theorem map_default (option : Option Q) (fallback : Q) :
    value (F := F) fq (option.getD fallback) = (option.map (value (F := F) fq)).getD (value (F := F) fq fallback) := by
  cases option <;> rfl

private theorem map_present (option : Option Q) :
    (option.map (value (F := F) fq)).isSome = option.isSome := by
  cases option <;> rfl

def inverse (q : Q) : Q := (ops.invert q).getD ops.zero
def root (q : Q) : Q := (ops.sqrt q).getD ops.zero

theorem inverse_value (q : Q) : value (F := F) fq (inverse fq api ops q) = (value (F := F) fq q)⁻¹ := by
  unfold inverse
  rw [map_default fq,ops.invertValue,ops.zeroValue]
  by_cases zero : value (F := F) fq q = 0 <;> simp [zero]

theorem root_value (q : Q) : value (F := F) fq (root fq api ops q) =
    ElligatorNativeRoots.rootValue api (value (F := F) fq q) := by
  unfold root
  rw [map_default fq,ops.sqrtValue,ops.zeroValue]
  rfl

theorem root_choice (q : Q) : (ops.sqrt q).isSome =
    ElligatorNativeRoots.choice api (value (F := F) fq q) := by
  rw [← map_present (F := F) (Q := Q) fq (ops.sqrt q),ops.sqrtValue]
  rfl

private theorem inverse_present (q : Q) : (ops.invert q).isSome = decide (value (F := F) fq q ≠ 0) := by
  rw [← map_present (F := F) (Q := Q) fq (ops.invert q),ops.invertValue]
  by_cases zero : value (F := F) fq q = 0 <;> simp [zero]

def parity (q : Q) : Bool := decide ((fq.bytes q ⟨0,by decide⟩).val % 2 = 1)

theorem byte_parity [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (q : Q) :
    parity fq q = decide (codec.decode (value (F := F) fq q) % 2 = 1) := by
  unfold parity value
  rw [fq.byteValue,TransferReduction.decode_canonical_cast codec _ (fq.bounded q)]
  have low := GroupScalarCodec.low_byte_bit (fq.integer q) 0 (by decide)
  simpa only [GroupByteCodec.littleEndianByte,Nat.mul_zero,pow_zero,Nat.div_one] using
    congrArg (fun n : Nat => decide (n = 1)) low

def coefficientK : F := -40964
def coefficientC1 : F := 40962 * (coefficientK : F)⁻¹
def coefficientC2 : F := (coefficientK : F)⁻¹ * (coefficientK : F)⁻¹

def constants : Q × Q × Q :=
  let k := ops.neg (ops.natural 40964)
  let inverseK := inverse fq api ops k
  (k,ops.mul (ops.natural 40962) inverseK,ops.mul inverseK inverseK)

def first (u : Q) : Q × Q × Q :=
  let c := constants fq api ops
  let tv := ops.mul (ops.natural 5) (ops.mul u u)
  let x := ops.mul (ops.neg c.2.1) (inverse fq api ops (ops.add (ops.natural 1) tv))
  let cubic := ops.mul (ops.add (ops.mul (ops.add x c.2.1) x) c.2.2) x
  (tv,x,cubic)

private theorem constants_value :
    value (F := F) fq (constants fq api ops).1 = (coefficientK : F) ∧
    value (F := F) fq (constants fq api ops).2.1 = (coefficientC1 : F) ∧
    value (F := F) fq (constants fq api ops).2.2 = (coefficientC2 : F) := by
  simp only [constants,ops.mulValue,inverse_value (F := F) fq api ops,ops.negValue,
    ops.naturalValue 40964 (by decide),ops.naturalValue 40962 (by decide),
    coefficientK,coefficientC1,coefficientC2]
  exact ⟨rfl,rfl,rfl⟩

theorem first_value (u : Q) :
    value (F := F) fq (first fq api ops u).1 = 5 * value (F := F) fq u * value (F := F) fq u ∧
    value (F := F) fq (first fq api ops u).2.1 = ElligatorNativeProgram.firstX coefficientC1 (value (F := F) fq u) ∧
    value (F := F) fq (first fq api ops u).2.2 = ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u) := by
  rcases constants_value (F := F) fq api ops with ⟨k,c1,c2⟩
  simp only [first,ops.mulValue,ops.addValue,ops.negValue,inverse_value (F := F) fq api ops,
    ops.naturalValue 5 (by decide),ops.naturalValue 1 (by decide),c1,c2,
    ElligatorNativeProgram.firstX,ElligatorNativeProgram.firstCubic,Elligator.cubic,
    Nat.cast_ofNat,Nat.cast_one,mul_assoc]
  trivial

def selected (u : Q) : Q × Q :=
  let f := first fq api ops u
  let choice := (ops.sqrt f.2.2).isSome
  (if choice then f.2.1 else ops.add (ops.neg f.2.1) (ops.neg (constants fq api ops).2.1),
   if choice then root fq api ops f.2.2 else root fq api ops (ops.mul f.1 f.2.2))

def selectedX (u : F) : F :=
  let x := ElligatorNativeProgram.firstX coefficientC1 u
  if ElligatorNativeRoots.choice api (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 u)
    then x else -x-coefficientC1

def selectedRoot (u : F) : F :=
  ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.selectedValue api 5 u
    (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 u))

theorem selected_value (u : Q) :
    value (F := F) fq (selected fq api ops u).1 = selectedX api (value (F := F) fq u) ∧
    value (F := F) fq (selected fq api ops u).2 = selectedRoot api (value (F := F) fq u) := by
  rcases first_value (F := F) fq api ops u with ⟨tv,x,cubic⟩
  have c1 := (constants_value (F := F) fq api ops).2.1
  have choice := root_choice fq api ops (first fq api ops u).2.2
  rw [cubic] at choice
  cases chosen : ElligatorNativeRoots.choice api
      (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)) <;>
    simp only [selected,choice,chosen,if_true,Bool.false_eq_true,if_false,
      root_value (F := F) fq api ops,ops.addValue,ops.negValue,ops.mulValue,tv,x,cubic,c1,
      selectedX,selectedRoot,ElligatorNativeRoots.selectedValue,sub_eq_add_neg] <;> trivial

def normalized (u : Q) : Q × Q :=
  let p := selected fq api ops u
  let choice := (ops.sqrt (first fq api ops u).2.2).isSome
  (p.1,if parity fq p.2 != choice then ops.neg p.2 else p.2)

theorem normalized_value [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (u : Q) :
    value (F := F) fq (normalized fq api ops u).1 = selectedX api (value (F := F) fq u) ∧
    value (F := F) fq (normalized fq api ops u).2 = ElligatorNativeParity.normalizeRoot codec
      (ElligatorNativeRoots.choice api (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)))
      (selectedRoot api (value (F := F) fq u)) := by
  have coordinates := selected_value (F := F) fq api ops u
  have choice := root_choice fq api ops (first fq api ops u).2.2
  rw [(first_value (F := F) fq api ops u).2.2] at choice
  refine ⟨coordinates.1,?_⟩
  simp only [normalized,byte_parity fq codec,choice]
  rw [coordinates.2]
  have parityBound := Nat.mod_lt (codec.decode (selectedRoot api (value (F := F) fq u))) (by decide : 0 < 2)
  rcases (show codec.decode (selectedRoot api (value (F := F) fq u)) % 2 = 0 ∨
      codec.decode (selectedRoot api (value (F := F) fq u)) % 2 = 1 from by omega) with even | odd
  · cases chosen : ElligatorNativeRoots.choice api
        (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)) <;>
      simp [even,chosen,ops.negValue,coordinates.2,ElligatorNativeParity.normalizeRoot]
  · cases chosen : ElligatorNativeRoots.choice api
        (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)) <;>
      simp [odd,chosen,ops.negValue,coordinates.2,ElligatorNativeParity.normalizeRoot]

def rational (u : Q) : Q × Q :=
  let p := normalized fq api ops u
  let k := (constants fq api ops).1
  let s := ops.mul p.1 k
  let t := ops.mul p.2 k
  let plus := ops.add s (ops.natural 1)
  let denominator := ops.mul plus t
  let inverseD := inverse fq api ops denominator
  (ops.mul (ops.mul inverseD plus) s,
    if (ops.invert denominator).isSome then
      ops.mul (ops.mul inverseD t) (ops.add s (ops.neg (ops.natural 1))) else ops.natural 1)

theorem rational_value [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (u : Q) :
    (⟨value (F := F) fq (rational fq api ops u).1,value (F := F) fq (rational fq api ops u).2⟩ : Group.Point F) =
      Elligator.rationalPoint
        (coefficientK * selectedX api (value (F := F) fq u))
        (coefficientK * ElligatorNativeParity.normalizeRoot codec
          (ElligatorNativeRoots.choice api (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)))
          (selectedRoot api (value (F := F) fq u))) := by
  have coordinates := normalized_value (F := F) fq api ops codec u
  have k := (constants_value (F := F) fq api ops).1
  simp only [rational,inverse_value (F := F) fq api ops,inverse_present fq api ops,
    ops.mulValue,ops.addValue,ops.negValue,ops.naturalValue 1 (by decide),coordinates.1,coordinates.2,k]
  simp only [mul_comm _ (coefficientK : F)]
  by_cases zero : (coefficientK * selectedX api (value (F := F) fq u) + 1) *
      (coefficientK * ElligatorNativeParity.normalizeRoot codec
        (ElligatorNativeRoots.choice api (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)))
        (selectedRoot api (value (F := F) fq u))) = 0
  · simp [Elligator.rationalPoint,zero,ops.naturalValue 1 (by decide),Nat.cast_one]
  · have factors := mul_ne_zero_iff.mp zero
    have nativeFactors := mul_ne_zero_iff.mp factors.2
    simp [Elligator.rationalPoint,zero,factors.1,nativeFactors.1,nativeFactors.2,
      inverse_value (F := F) fq api ops,
      ops.mulValue,ops.addValue,ops.negValue,ops.naturalValue 1 (by decide),
      coordinates.1,coordinates.2,k,Nat.cast_one,sub_eq_add_neg,mul_comm,mul_left_comm,mul_assoc]

/-- Only unmodified raw Affine→Extended and clear_cofactor operations are
contracted. The raw coordinate law applies only to points already proved on
the curve; it does not assert that arbitrary unchecked inputs are group points.
The exact upstream embed/promote objects are shared with the SDK reader. -/
structure PointPrimitives (fq : GroupNativeSdk.FqBytes Q) {E S R K Signing J : Type} [AddCommGroup J]
    {fr : GroupNativeSdk.FrBytes R} {d : F} {model : Group.StandardCurveModel J d}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model) where
  raw : Q → Q → E
  clear : E → S
  rawCoordinates : ∀ x y, Group.OnCurve d (⟨value (F := F) fq x,value (F := F) fq y⟩ : Group.Point F) →
    model.coordinates (upstream.embed (raw x y)) = ⟨value (F := F) fq x,value (F := F) fq y⟩
  clearEmbedding : ∀ point, upstream.embed (upstream.promote (clear point)) = 8 • upstream.embed point

def toSubgroup {E S R K Signing J : Type} [AddCommGroup J]
    {fr : GroupNativeSdk.FrBytes R} {d : F} {model : Group.StandardCurveModel J d}
    {upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model}
    (points : PointPrimitives fq upstream) (u : Q) : S :=
  let p := rational fq api ops u
  points.clear (points.raw p.1 p.2)

private theorem raw_curve [CharP F Scalar.modulus] [Fintype F]
    (ops : Primitives fq api) (codec : TransferReduction.CanonicalField F) (d : F) (u : Q)
    (kNonzero : (coefficientK : F) ≠ 0) (denominator : Group.NoUnitSquare (-5 : F))
    (edwards : (coefficientK : F) * d = 40960)
    (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1) :
    Group.OnCurve d (Elligator.rationalPoint
      (coefficientK * selectedX api (value (F := F) fq u))
      (coefficientK * ElligatorNativeParity.normalizeRoot codec
        (ElligatorNativeRoots.choice api (ElligatorNativeProgram.firstCubic coefficientC1 coefficientC2 (value (F := F) fq u)))
        (selectedRoot api (value (F := F) fq u)))) := by
  let input := value (F := F) fq u
  let x := ElligatorNativeProgram.firstX (coefficientC1 : F) input
  let first := ElligatorNativeProgram.firstCubic (coefficientC1 : F) coefficientC2 input
  let choice := ElligatorNativeRoots.choice api first
  let y := ElligatorNativeParity.normalizeRoot codec choice (selectedRoot api input)
  have denNonzero := Elligator.first_denominator_nonzero (5 : F) input denominator
  have coordinate : (1 + 5 * input * input) * x = -(coefficientC1 : F) := by
    dsimp only [x,ElligatorNativeProgram.firstX]
    calc
      _ = -(coefficientC1 : F) * ((1 + 5 * input * input) * (1 + 5 * input * input)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ denNonzero,mul_one]
  have rootSquare := (ElligatorNativeRoots.computed_roots api odd 5 input first fiveNonzero fiveEuler).2
  have normalizedSquare : y*y = if choice then first else 5*input*input*first :=
    (ElligatorNativeParity.normalize_square codec choice (selectedRoot api input)).trans rootSquare
  have selectedSquare : y*y = Elligator.cubic (coefficientC1 : F) coefficientC2 (selectedX api input) := by
    cases selected : choice
    · simpa only [selectedX,choice,x,first,selected,Bool.false_eq_true,if_false,
        Elligator.alternative_cubic coefficientC1 coefficientC2 x (5*input*input) coordinate] using normalizedSquare
    · simpa only [selectedX,choice,x,first,selected,if_true] using normalizedSquare
  have c1 : (coefficientK : F) * coefficientC1 = 40962 := by
    unfold coefficientC1
    calc
      _ = 40962 * ((coefficientK : F) * coefficientK⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ kNonzero,mul_one]
  have c2 : (coefficientK : F) * coefficientK * coefficientC2 = 1 := by
    unfold coefficientC2
    calc
      _ = ((coefficientK : F) * coefficientK⁻¹) * (coefficientK * coefficientK⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ kNonzero,one_mul]
  apply ElligatorCurve.rational_on_curve coefficientK 40962 d _ _ kNonzero
  · norm_num [coefficientK]
  · convert edwards using 1 <;> norm_num
  · exact ElligatorCurve.scaled_cubic coefficientK 40962 coefficientC1 coefficientC2 _ _ c1 c2 selectedSquare

theorem to_subgroup_coordinates {E S R K Signing J : Type} [AddCommGroup J]
    [CharP F Scalar.modulus] [Fintype F]
    {fr : GroupNativeSdk.FrBytes R} {d : F} {model : Group.StandardCurveModel J d}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (points : PointPrimitives fq upstream) (codec : TransferReduction.CanonicalField F)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (kNonzero : (coefficientK : F) ≠ 0) (denominator : Group.NoUnitSquare (-5 : F))
    (edwards : (coefficientK : F) * d = 40960)
    (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1) (u : Q) :
    model.coordinates (upstream.embed (upstream.promote (toSubgroup fq api ops points u))) =
      ElligatorNativeProgram.generatorValue codec api coefficientC1 coefficientC2 coefficientK d (value (F := F) fq u) := by
  let p := rational fq api ops u
  have raw := rational_value (F := F) fq api ops codec u
  have curve := raw_curve fq api ops codec d u kNonzero denominator edwards odd fiveNonzero fiveEuler
  have curveP : Group.OnCurve d (⟨value (F := F) fq p.1,value (F := F) fq p.2⟩ : Group.Point F) := by
    change Group.OnCurve d (⟨value (F := F) fq (rational fq api ops u).1,value (F := F) fq (rational fq api ops u).2⟩ : Group.Point F)
    rw [raw]
    exact curve
  have rawMeaning := points.rawCoordinates p.1 p.2 curveP
  dsimp only [p] at rawMeaning
  unfold toSubgroup
  rw [points.clearEmbedding,← GroupNativeCofactor.native_eight_coordinates d imaginary model nonSquare imaginarySquare,
    rawMeaning,raw]
  rfl

set_option pp.all true in
#check @inverse_value
#print axioms inverse_value
set_option pp.all true in
#check @root_value
#print axioms root_value
set_option pp.all true in
#check @root_choice
#print axioms root_choice
set_option pp.all true in
#check @byte_parity
#print axioms byte_parity
set_option pp.all true in
#check @first_value
#print axioms first_value
set_option pp.all true in
#check @selected_value
#print axioms selected_value
set_option pp.all true in
#check @normalized_value
#print axioms normalized_value
set_option pp.all true in
#check @rational_value
#print axioms rational_value
set_option pp.all true in
#check @to_subgroup_coordinates
#print axioms to_subgroup_coordinates

end ShielddSecurity.NativeAssetMap
