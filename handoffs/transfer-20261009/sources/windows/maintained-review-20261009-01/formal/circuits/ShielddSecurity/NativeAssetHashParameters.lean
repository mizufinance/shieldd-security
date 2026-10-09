import ShielddSecurity.NativeAssetHash

set_option maxHeartbeats 300000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeAssetHashParameters

variable {F Q Encoded : Type} [Field F] [CharP F Scalar.modulus]
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

/- The small signed table is the actual qualified RNK Data2 parameter table.
Its independent canonical SDK artifact entries and signed representation have
already been checked entry by entry. No caller-selected coefficients or hash
result are supplied to this instance. Hex decoding and Jubjub Fq arithmetic/
codec laws are global unmodified primitive contracts; the owned field wrapper,
byte reversal, Option ordering, row/height/header guards and load are separate
proved definitions consumed below. Serde/native source instantiation remains
visible in the accompanying source map, rather than a HashMapABI assumption. -/

def smallParameters : Poseidon.Parameters F 3 :=
  Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters

theorem small_ark_field (row : Fin 65) (column : Fin 3) :
    ShielddNativeParameterBytes.fieldBody hex fq
      (hex.render (RuntimeNativePoseidonParameters.smallCanonical.ark row.val column)) =
      some (ShielddNativeIvkHash.sdkConstant fq arithmetic codec
        (smallParameters.ark row.val column)) := by
  have checks := RuntimeNativePoseidonParameters.small_ark_entries row column
  rw [RuntimeNativePoseidonParameters.small_parameters] at checks
  exact (ShielddNativeParameterLoader.coefficient_loaded hex fq arithmetic codec
    _ _ checks.1 checks.2).1

theorem small_mds_field (row column : Fin 3) :
    ShielddNativeParameterBytes.fieldBody hex fq
      (hex.render (RuntimeNativePoseidonParameters.smallCanonical.mds row column)) =
      some (ShielddNativeIvkHash.sdkConstant fq arithmetic codec
        (smallParameters.mds row column)) := by
  have checks := RuntimeNativePoseidonParameters.small_mds_entries row column
  rw [RuntimeNativePoseidonParameters.small_parameters] at checks
  exact (ShielddNativeParameterLoader.coefficient_loaded hex fq arithmetic codec
    _ _ checks.1 checks.2).1

def loadSmall : Option (ShielddNativeLoadedPermutation.NativePermutation Q 3) :=
  ShielddNativeLoadedPermutation.loadParameters hex fq
    ShielddNativeLoadedPermutation.sourceHeader
    (fun row => RuntimeNativePoseidonParameters.smallCanonical.ark row.val)
    RuntimeNativePoseidonParameters.smallCanonical.mds

theorem small_instance :
    loadSmall hex fq = some
      (ShielddNativeLoadedPermutation.expectedNative fq arithmetic codec smallParameters) := by
  exact ShielddNativeLoadedPermutation.small_loaded hex fq arithmetic codec

/- The successful loader has exactly65 ARK rows. The total fallback of this
indexed loop is never used by the proved bounded prefix or the full65 loop.
Each step reads the actual native coefficient objects from that loaded value. -/
def loadedRound {width : Nat}
    (parameters : ShielddNativeLoadedPermutation.NativePermutation Q width)
    (index : Nat) (state : Poseidon.State Q width) : Poseidon.State Q width :=
  if within : index < 65 then
    ShielddNativeLoadedPermutation.nativeRound fq arithmetic square parameters
      ⟨index, within⟩ state
  else state

def loadedRounds {width : Nat}
    (parameters : ShielddNativeLoadedPermutation.NativePermutation Q width) :
    Nat → Poseidon.State Q width → Poseidon.State Q width
  | 0, state => state
  | count + 1, state => loadedRound fq arithmetic square parameters count
      (loadedRounds parameters count state)

theorem rounds_consumer {width : Nat} (parameters : Poseidon.Parameters F width)
    (count : Nat) (state : Poseidon.State Q width) (bounded : count ≤ 65) :
    loadedRounds fq arithmetic square
      (ShielddNativeLoadedPermutation.expectedNative fq arithmetic codec parameters)
      count state =
    ShielddNativeRnkHash.rounds fq arithmetic square codec parameters count state := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
    intro bounded
    have within : count < 65 := by omega
    have previous := ih (by omega : count ≤ 65)
    change loadedRound fq arithmetic square _ count
      (loadedRounds fq arithmetic square _ count state) =
        ShielddNativeRnkHash.round fq arithmetic square codec parameters count
          (ShielddNativeRnkHash.rounds fq arithmetic square codec parameters count state)
    rw [previous]
    unfold loadedRound
    rw [dif_pos within]
    exact ShielddNativeLoadedPermutation.round_consumer fq arithmetic square codec
      parameters ⟨count, within⟩ _

/- Actual poseidon::hash selects SMALL for this singleton input, places282 in
lane0, adds the asset to lane1, leaves lane2 untouched, runs the loaded65 ARK
rows and returns lane1. Loading failure propagates through Option. Success is
derived from the actual embedded table instance, not taken as a premise. -/
def assetSource (asset : Q) : Option Q :=
  (loadSmall hex fq).map (fun parameters =>
    loadedRounds fq arithmetic square parameters 65
      (ShielddNativeRnkHash.absorb fq arithmetic
        (ShielddNativeRnkHash.initialState fq arithmetic initial 3 26 1) [asset])
      ⟨1, by decide⟩)

theorem asset_source_object (asset : Q) :
    assetSource hex fq arithmetic initial square asset =
      some (NativeAssetHash.block fq arithmetic initial square codec smallParameters asset) := by
  unfold assetSource
  rw [small_instance hex fq arithmetic codec]
  simp only [Option.map_some]
  rw [rounds_consumer fq arithmetic square codec _ 65 _ (by decide)]
  rfl

include codec in
theorem asset_source_value (asset : Q) :
    (assetSource hex fq arithmetic initial square asset).map
      (fun value => (fq.integer value : F)) =
      some (Poseidon.hash3 smallParameters 26 [(fq.integer asset : F)]) := by
  rw [asset_source_object hex fq arithmetic initial square codec]
  simp only [Option.map_some]
  rw [NativeAssetHash.block_value fq arithmetic initial square codec smallParameters asset]

set_option pp.all true in
#check @small_ark_field
#print axioms small_ark_field
set_option pp.all true in
#check @small_mds_field
#print axioms small_mds_field
set_option pp.all true in
#check @small_instance
#print axioms small_instance
set_option pp.all true in
#check @rounds_consumer
#print axioms rounds_consumer
set_option pp.all true in
#check @asset_source_object
#print axioms asset_source_object
set_option pp.all true in
#check @asset_source_value
#print axioms asset_source_value

end ShielddSecurity.NativeAssetHashParameters
