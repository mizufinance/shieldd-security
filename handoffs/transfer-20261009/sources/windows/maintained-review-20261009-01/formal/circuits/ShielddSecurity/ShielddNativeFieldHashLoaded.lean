import ShielddSecurity.NativeAssetHashParameters
import ShielddSecurity.ShielddNativeFieldHash

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.ShielddNativeFieldHashLoaded

variable {F Q Encoded : Type} [Field F] [CharP F Scalar.modulus]
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

def wideParameters : Poseidon.Parameters F 6 :=
  Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters

def loadWide : Option (ShielddNativeLoadedPermutation.NativePermutation Q 6) :=
  ShielddNativeLoadedPermutation.loadParameters hex fq ShielddNativeLoadedPermutation.sourceHeader
    (fun row => RuntimeNativePoseidonParameters.wideCanonical.ark row.val)
    RuntimeNativePoseidonParameters.wideCanonical.mds

theorem wide_instance : loadWide hex fq = some
    (ShielddNativeLoadedPermutation.expectedNative fq arithmetic codec wideParameters) := by
  exact ShielddNativeLoadedPermutation.wide_loaded hex fq arithmetic codec

def loadedFold {width : Nat}
    (parameters : ShielddNativeLoadedPermutation.NativePermutation Q width)
    (chunks : List (List Q)) (state : Poseidon.State Q width) : Poseidon.State Q width :=
  chunks.foldl (fun current chunk =>
    NativeAssetHashParameters.loadedRounds fq arithmetic square parameters 65
      (ShielddNativeRnkHash.absorb fq arithmetic current chunk)) state

/-- Each loaded round reads actual parsed ARK/MDS entries. This recurrence
extends the independently audited 65-round consumer to arbitrary finite chunks. -/
theorem fold_consumer {width : Nat} (parameters : Poseidon.Parameters F width)
    (chunks : List (List Q)) (state : Poseidon.State Q width) :
    loadedFold fq arithmetic square
      (ShielddNativeLoadedPermutation.expectedNative fq arithmetic codec parameters) chunks state =
      chunks.foldl (fun current chunk => ShielddNativeRnkHash.rounds fq arithmetic square codec
        parameters 65 (ShielddNativeRnkHash.absorb fq arithmetic current chunk)) state := by
  induction chunks generalizing state with
  | nil => rfl
  | cons head tail ih =>
    simp only [loadedFold, List.foldl_cons] at ih ⊢
    rw [ih, NativeAssetHashParameters.rounds_consumer fq arithmetic square codec
      parameters 65 _ (by decide)]

def loadedSponge {width : Nat}
    (parameters : ShielddNativeLoadedPermutation.NativePermutation Q width)
    (domain arity : Nat) (chunks : List (List Q)) : Poseidon.State Q width :=
  match chunks with
  | [] => NativeAssetHashParameters.loadedRounds fq arithmetic square parameters 65
      (ShielddNativeRnkHash.initialState fq arithmetic initial width domain arity)
  | _ :: _ => loadedFold fq arithmetic square parameters chunks
      (ShielddNativeRnkHash.initialState fq arithmetic initial width domain arity)

theorem sponge_consumer {width : Nat} (parameters : Poseidon.Parameters F width)
    (domain arity : Nat) (chunks : List (List Q)) :
    loadedSponge fq arithmetic initial square
      (ShielddNativeLoadedPermutation.expectedNative fq arithmetic codec parameters) domain arity chunks =
      ShielddNativeRnkHash.sponge fq arithmetic initial square codec parameters domain arity chunks := by
  cases chunks with
  | nil =>
    simpa only [loadedSponge, ShielddNativeRnkHash.sponge] using
      (NativeAssetHashParameters.rounds_consumer fq arithmetic square codec
        parameters 65 (ShielddNativeRnkHash.initialState fq arithmetic initial width domain arity)
        (by decide))
  | cons head tail =>
    simpa only [loadedSponge, ShielddNativeRnkHash.sponge] using
      (fold_consumer fq arithmetic square codec parameters (head :: tail)
        (ShielddNativeRnkHash.initialState fq arithmetic initial width domain arity))

/-- The owned public callback selects its actual embedded recipe and rate,
propagates load failure, handles empty input, and retains the finite u64 IV guard.
Hex parsing/Fq arithmetic and codec laws are global primitive contracts. -/
def loadedHash (domain : Nat) (inputs : List Q) : Option Q :=
  if inputs.length * 256 + domain < 2^64 then
    if inputs.length ≤ 2 then
      (NativeAssetHashParameters.loadSmall hex fq).map (fun parameters =>
        loadedSponge fq arithmetic initial square parameters domain inputs.length
          (Poseidon.chunks2 inputs) ⟨1, by decide⟩)
    else (loadWide hex fq).map (fun parameters =>
      loadedSponge fq arithmetic initial square parameters domain inputs.length
        (Poseidon.chunks5 inputs) ⟨1, by decide⟩)
  else none

theorem hash_object (domain : Nat) (inputs : List Q)
    (bounded : inputs.length * 256 + domain < 2^64) :
    loadedHash hex fq arithmetic initial square domain inputs = some
      (ShielddNativeRnkHash.hash fq arithmetic initial square codec
        NativeAssetHashParameters.smallParameters wideParameters domain inputs) := by
  unfold loadedHash ShielddNativeRnkHash.hash
  rw [if_pos bounded, if_pos bounded]
  by_cases short : inputs.length ≤ 2
  · rw [if_pos short, if_pos short,
      NativeAssetHashParameters.small_instance hex fq arithmetic codec]
    simp only [Option.map_some]
    rw [sponge_consumer fq arithmetic initial square codec]
  · rw [if_neg short, if_neg short, wide_instance hex fq arithmetic codec]
    simp only [Option.map_some]
    rw [sponge_consumer fq arithmetic initial square codec]

/-- Both recipes and successful loading are derived from the retained actual
parameter instances. No per-call native result or caller-selected table is assumed. -/
theorem hash_value (codec : TransferReduction.CanonicalField F) (domain : Nat) (inputs : List Q)
    (bounded : inputs.length * 256 + domain < 2^64) :
    (loadedHash hex fq arithmetic initial square domain inputs).map
      (ShielddNativeIvkHash.fqValue (F := F) fq) = some
      (Poseidon.hash NativeAssetHashParameters.smallParameters wideParameters domain
        (inputs.map (ShielddNativeIvkHash.fqValue (F := F) fq))) := by
  rw [hash_object hex fq arithmetic initial square codec domain inputs bounded]
  simp only [Option.map_some]
  rw [ShielddNativeFieldHash.hash_value fq arithmetic initial square codec
    NativeAssetHashParameters.smallParameters wideParameters domain inputs bounded]

set_option pp.all true in
#check @wide_instance
#print axioms wide_instance
set_option pp.all true in
#check @fold_consumer
#print axioms fold_consumer
set_option pp.all true in
#check @sponge_consumer
#print axioms sponge_consumer
set_option pp.all true in
#check @hash_object
#print axioms hash_object
set_option pp.all true in
#check @hash_value
#print axioms hash_value

end ShielddSecurity.ShielddNativeFieldHashLoaded
