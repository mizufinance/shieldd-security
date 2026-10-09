import ShielddSecurity.NativeTransferAdmission

set_option maxHeartbeats 300000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeBalanceCommitment

/-! One-asset projection of the pinned SDK TransferPlan.balance fold. The
spends and outputs are accumulated separately. Same-sign NonZeroU128 addition
panics on overflow; `none` denotes that unsuccessful source path, not a runtime
Result or a field-wrapped balance. Zero entries are omitted by the SDK map. -/

def checkedTotal (amounts : NativeTransferAdmission.Amounts) : Option Nat :=
  if amounts.1.val + amounts.2.val < 2^128 then
    some (amounts.1.val + amounts.2.val) else none

inductive Net where
  | balanced
  | provided (amount : Nat)
  | required (amount : Nat)
  deriving DecidableEq

def canonicalNet (inputs outputs : Nat) : Net :=
  if inputs = outputs then .balanced else
    if inputs < outputs then .required (outputs-inputs) else .provided (inputs-outputs)

def signedValue : Net → Int
  | .balanced => 0
  | .provided amount => (amount : Int)
  | .required amount => -(amount : Int)

def sdkNet (inputs outputs : NativeTransferAdmission.Amounts) : Option Net :=
  match checkedTotal inputs, checkedTotal outputs with
  | some input, some output => some (canonicalNet input output)
  | _, _ => none

def sdkCommitment {J : Type} [AddCommGroup J] (base blindingBase : J)
    (net : Net) (blinding : Nat) : J :=
  signedValue net • base + blinding • blindingBase

theorem checked_total_success (amounts : NativeTransferAdmission.Amounts) (total : Nat)
    (success : checkedTotal amounts = some total) :
    total = amounts.1.val + amounts.2.val ∧ total < 2^128 := by
  unfold checkedTotal at success
  split at success
  · rename_i bounded
    have same := Option.some.inj success
    exact ⟨same.symm, same ▸ bounded⟩
  · cases success

theorem checked_total_overflow (amounts : NativeTransferAdmission.Amounts)
    (overflow : 2^128 ≤ amounts.1.val + amounts.2.val) : checkedTotal amounts = none := by
  simp only [checkedTotal,if_neg (Nat.not_lt.mpr overflow)]

theorem canonical_net_value (inputs outputs : Nat) :
    signedValue (canonicalNet inputs outputs) = (inputs : Int) - (outputs : Int) := by
  unfold canonicalNet
  split <;> rename_i branch
  · simp only [signedValue]; omega
  · split <;> simp only [signedValue] <;> omega

theorem sdk_net_success (inputs outputs : NativeTransferAdmission.Amounts) (net : Net)
    (success : sdkNet inputs outputs = some net) :
    inputs.1.val + inputs.2.val < 2^128 ∧
    outputs.1.val + outputs.2.val < 2^128 ∧
    net = canonicalNet (inputs.1.val + inputs.2.val) (outputs.1.val + outputs.2.val) := by
  cases inputEq : checkedTotal inputs with
  | none => simp only [sdkNet,inputEq] at success; cases success
  | some input =>
    cases outputEq : checkedTotal outputs with
    | none => simp only [sdkNet,inputEq,outputEq] at success; cases success
    | some output =>
      have inputFact := checked_total_success inputs input inputEq
      have outputFact := checked_total_success outputs output outputEq
      simp only [sdkNet,inputEq,outputEq] at success
      have same := Option.some.inj success
      exact ⟨by omega,by omega,by rw [← inputFact.1,← outputFact.1]; exact same.symm⟩

theorem sdk_commitment_value {J : Type} [AddCommGroup J] (base blindingBase : J)
    (inputs outputs : NativeTransferAdmission.Amounts) (net : Net) (blinding : Nat)
    (success : sdkNet inputs outputs = some net) :
    sdkCommitment base blindingBase net blinding =
      (inputs.1.val + inputs.2.val) • base -
      (outputs.1.val + outputs.2.val) • base + blinding • blindingBase := by
  have observed := sdk_net_success inputs outputs net success
  unfold sdkCommitment
  rw [observed.2.2,canonical_net_value,sub_zsmul]
  simp only [natCast_zsmul,sub_eq_add_neg]

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]

theorem decoded_amount_sum (codec : TransferReduction.CanonicalField F)
    (amounts : NativeTransferAdmission.Amounts) :
    codec.decode (NativeTransferAdmission.sumAmounts amounts) = amounts.1.val + amounts.2.val := by
  have capacity : 2^129 < Scalar.modulus := by decide
  have left := amounts.1.isLt
  have right := amounts.2.isLt
  have bound : amounts.1.val + amounts.2.val < Scalar.modulus := by omega
  unfold NativeTransferAdmission.sumAmounts
  rw [← Nat.cast_add]
  exact TransferReduction.decode_canonical_cast codec _ bound

/-- Negation is derived from the full Edwards model, not supplied as a
per-output equality. This is the exact owned `output.x = -output.x` operation. -/
theorem coordinates_neg {J : Type} [AddCommGroup J] (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (point : J) :
    model.coordinates (-point) = ⟨-(model.coordinates point).x,(model.coordinates point).y⟩ := by
  let inverse : Group.Point F := ⟨-(model.coordinates point).x,(model.coordinates point).y⟩
  have curve : Group.OnCurve d inverse := by
    simpa only [Group.OnCurve,inverse,mul_neg,neg_mul,neg_neg] using model.onCurve point
  obtain ⟨other,otherCoordinates⟩ := model.covers inverse curve
  have denominators := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    (model.coordinates point) inverse (model.onCurve point) curve
  have crossZero : Group.cross (model.coordinates point) inverse = 0 := by
    unfold Group.cross inverse
    ring
  have diagonalValue : Group.diagonal (model.coordinates point) inverse =
      1 - Group.delta d (model.coordinates point) inverse := by
    calc
      _ = (model.coordinates point).y * (model.coordinates point).y -
          (model.coordinates point).x * (model.coordinates point).x := by
        unfold Group.diagonal inverse; ring
      _ = _ := by
        rw [model.onCurve point]
        unfold Group.delta inverse
        ring
  have zeroCoordinates : model.coordinates (point+other) = model.coordinates 0 := by
    rw [model.addition,otherCoordinates,model.identity]
    simp only [Group.affineAdd,crossZero,diagonalValue,zero_div,
      div_self denominators.2,Group.identityPoint]
  have sumZero := model.injective zeroCoordinates
  have otherNeg : other = -point := by
    calc
      other = 0+other := (zero_add other).symm
      _ = (-point+point)+other := by rw [neg_add_cancel]
      _ = -point+(point+other) := add_assoc _ _ _
      _ = -point := by rw [sumZero,add_zero]
  rw [← otherNeg]
  exact otherCoordinates

/-- Join SDK canonical signed-imbalance commitment to the owned native
statement balance. The independent successful SDK fold excludes its panic
path; native success supplies the actual scalar/generator admission guards.
SDK Fr/group encoding and generator bindings are global source ABI joins. -/
theorem native_balance_commitment {J : Type} [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (two : (2 : F) ≠ 0) (base blindingBase : J) (asset : F)
    (inputs outputs : NativeTransferAdmission.Amounts) (blinding : F) (net : Net)
    (sdkSuccess : sdkNet inputs outputs = some net) (value : Group.Point F)
    (nativeSuccess : NativeTransferAdmission.balanceNative codec writer d
      (fun _ => model.coordinates base) (model.coordinates blindingBase)
      asset inputs outputs blinding = .ok value) :
    value = model.coordinates (sdkCommitment base blindingBase net (codec.decode blinding)) := by
  by_cases canonical : codec.decode blinding < Scalar.order
  · by_cases identity : NativeTransferAdmission.isIdentity (model.coordinates base) = true
    · simp only [NativeTransferAdmission.balanceNative,if_pos canonical,identity,if_true] at nativeSuccess
      cases nativeSuccess
    · have cleared : NativeTransferAdmission.isIdentity (model.coordinates base) = false := by
        cases observed : NativeTransferAdmission.isIdentity (model.coordinates base) <;> simp_all
      simp only [NativeTransferAdmission.balanceNative,if_pos canonical,cleared,Bool.false_eq_true,if_false,
        NativeTransferAdmission.nativeMultiply] at nativeSuccess
      rw [GroupByteCodec.native_reader_coordinates codec writer d imaginary model nonSquare imaginarySquare two,
        GroupByteCodec.native_reader_coordinates codec writer d imaginary model nonSquare imaginarySquare two,
        GroupByteCodec.native_reader_coordinates codec writer d imaginary model nonSquare imaginarySquare two,
        decoded_amount_sum,decoded_amount_sum,
        ← coordinates_neg d imaginary model nonSquare imaginarySquare,
        GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare,
        GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare] at nativeSuccess
      have equal := Except.ok.inj nativeSuccess
      rw [sdk_commitment_value base blindingBase inputs outputs net (codec.decode blinding) sdkSuccess]
      simpa only [sub_eq_add_neg] using equal.symm
  · simp only [NativeTransferAdmission.balanceNative,if_neg canonical] at nativeSuccess
    cases nativeSuccess

set_option pp.all true in
#check @checked_total_success
#print axioms checked_total_success
set_option pp.all true in
#check @checked_total_overflow
#print axioms checked_total_overflow
set_option pp.all true in
#check @canonical_net_value
#print axioms canonical_net_value
set_option pp.all true in
#check @sdk_net_success
#print axioms sdk_net_success
set_option pp.all true in
#check @sdk_commitment_value
#print axioms sdk_commitment_value
set_option pp.all true in
#check @decoded_amount_sum
#print axioms decoded_amount_sum
set_option pp.all true in
#check @coordinates_neg
#print axioms coordinates_neg
set_option pp.all true in
#check @native_balance_commitment
#print axioms native_balance_commitment

end ShielddSecurity.NativeBalanceCommitment
