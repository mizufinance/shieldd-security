import ShielddSecurity.ShielddNativeIvkSource

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeIvkSdkProgram

variable {F : Type} [Field F] {Q : Type}

/-- Named global ff::Field square primitive. The law concerns every Fq value;
it contains no key, witness column, permutation result or security conclusion. -/
structure SquarePrimitive (fq : GroupNativeSdk.FqBytes Q) where
  square : Q → Q
  squareValue : ∀ input,
    ShielddNativeIvkHash.fqValue (F := F) fq (square input) =
      ShielddNativeIvkHash.fqValue (F := F) fq input * ShielddNativeIvkHash.fqValue (F := F) fq input

variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

/-- The exact SDK lane expression: add the parsed ARK value, then execute
square().square()*value for the first/last four rounds and lane zero. Other
lanes retain the shifted value. Parameter-instance/source-byte linkage remains
separate from these globally defined loader and arithmetic expressions. -/
def transform (parameters : Poseidon.Parameters F 6) (index : Nat)
    (state : Poseidon.State Q 6) (column : Fin 6) : Q :=
  let shifted := arithmetic.add (state column)
    (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (parameters.ark index column))
  if Poseidon.nonlinear index column.val then
    arithmetic.mul (square.square (square.square shifted)) shifted else shifted

theorem transform_value (parameters : Poseidon.Parameters F 6) (index : Nat)
    (state : Poseidon.State Q 6) (column : Fin 6) :
    ShielddNativeIvkHash.fqValue (F := F) fq (transform fq arithmetic square codec parameters index state column) =
      let shifted := ShielddNativeIvkHash.fqValue (F := F) fq (state column) + parameters.ark index column
      if Poseidon.nonlinear index column.val then shifted ^ 5 else shifted := by
  unfold transform
  split <;> simp_all only [arithmetic.mulValue,square.squareValue,arithmetic.addValue,
    ShielddNativeIvkHash.sdk_constant_value]
  · ring

/-- SDK MDS zip/fold uses the actual Fq::ZERO constructor, not a fabricated
parameter coefficient zero. Each coefficient is the defined canonical LE
parser result of the corresponding mathematical parameter entry. -/
def round (parameters : Poseidon.Parameters F 6) (index : Nat)
    (state : Poseidon.State Q 6) : Poseidon.State Q 6 := fun row =>
  (List.finRange 6).foldl (fun total column => arithmetic.add total
    (arithmetic.mul (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (parameters.mds row column))
      (transform fq arithmetic square codec parameters index state column))) arithmetic.zero

include initial in
theorem round_value (parameters : Poseidon.Parameters F 6) (index : Nat)
    (state : Poseidon.State Q 6) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (round fq arithmetic square codec parameters index state column)) =
      Poseidon.round parameters index (fun column => ShielddNativeIvkHash.fqValue (F := F) fq (state column)) := by
  funext row
  have folded := Poseidon.fold_evaluates (ShielddNativeIvkHash.sdkOperations fq arithmetic codec)
    (ShielddNativeIvkHash.fqValue (F := F) fq)
    (ShielddNativeIvkHash.sdk_operations_evaluate fq arithmetic codec) (List.finRange 6)
    (fun column => arithmetic.mul
      (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (parameters.mds row column))
      (transform fq arithmetic square codec parameters index state column)) arithmetic.zero
  dsimp only [ShielddNativeIvkHash.sdkOperations] at folded
  unfold round
  rw [folded]
  simp only [initial.zeroValue,arithmetic.mulValue,ShielddNativeIvkHash.sdk_constant_value,
    transform_value]
  rfl

/-- The iterator's symbolic prefix recurrence. It neither unrolls 65 rounds
nor supplies the desired output as an induction premise. -/
def rounds (parameters : Poseidon.Parameters F 6) : Nat → Poseidon.State Q 6 → Poseidon.State Q 6
  | 0, state => state
  | count+1, state => round fq arithmetic square codec parameters count
      (rounds parameters count state)

include initial in
theorem rounds_value (parameters : Poseidon.Parameters F 6) (count : Nat) (state : Poseidon.State Q 6) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (rounds fq arithmetic square codec parameters count state column)) =
      Poseidon.rounds parameters count (fun column => ShielddNativeIvkHash.fqValue (F := F) fq (state column)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
        (round fq arithmetic square codec parameters count
          (rounds fq arithmetic square codec parameters count state) column)) = _
      rw [round_value fq arithmetic initial square codec,ih]
      rfl

def ivk (parameters : Poseidon.Parameters F 6) (nk x y : Q) : Q :=
  rounds fq arithmetic square codec parameters 65
    (ShielddNativeIvkSource.sdkInitial fq arithmetic initial nk x y) ⟨1,by decide⟩

theorem ivk_value (parameters : Poseidon.Parameters F 6) (nk x y : Q) :
    ShielddNativeIvkHash.fqValue (F := F) fq (ivk fq arithmetic initial square codec parameters nk x y) =
      Poseidon.hash6 parameters 16 [ShielddNativeIvkHash.fqValue (F := F) fq nk,
        ShielddNativeIvkHash.fqValue (F := F) fq x,ShielddNativeIvkHash.fqValue (F := F) fq y] := by
  have direct := congrArg (fun state : Poseidon.State F 6 => state ⟨1,by decide⟩)
    (rounds_value fq arithmetic initial square codec parameters 65
      (ShielddNativeIvkSource.sdkInitial fq arithmetic initial nk x y))
  have multiplyBody := congrArg (fun state : Poseidon.State F 6 => state ⟨1,by decide⟩)
    (Poseidon.rounds_evaluate (ShielddNativeIvkHash.sdkOperations fq arithmetic codec)
      (ShielddNativeIvkHash.fqValue (F := F) fq)
      (ShielddNativeIvkHash.sdk_operations_evaluate fq arithmetic codec) parameters 65
      (ShielddNativeIvkSource.sdkInitial fq arithmetic initial nk x y))
  exact (direct.trans multiplyBody.symm).trans
    (ShielddNativeIvkSource.sdk_ivk_value fq arithmetic initial codec parameters nk x y)

set_option pp.all true in
#check @transform_value
#print axioms transform_value
set_option pp.all true in
#check @round_value
#print axioms round_value
set_option pp.all true in
#check @rounds_value
#print axioms rounds_value
set_option pp.all true in
#check @ivk_value
#print axioms ivk_value

end ShielddSecurity.ShielddNativeIvkSdkProgram
