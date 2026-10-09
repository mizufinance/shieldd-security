import ShielddSecurity.ShielddNativeLoadedPermutation

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeAssetHash

variable {F Q : Type} [Field F]
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

/-- Exact native poseidon::hash ASSET_GENERATOR specialization: one Fq input,
small width3/rate2, domain26, IV282, one65-round block and output lane1.
The actual loaded ARK/MDS instance is supplied separately by the owned loader
and its original parameter-entry certificates, not by a hash-result premise. -/
def block (small : Poseidon.Parameters F 3) (asset : Q) : Q :=
  ShielddNativeRnkHash.rounds fq arithmetic square codec small 65
    (ShielddNativeRnkHash.absorb fq arithmetic
      (ShielddNativeRnkHash.initialState fq arithmetic initial 3 26 1) [asset])
    ⟨1,by decide⟩

theorem source_callback (small : Poseidon.Parameters F 3)
    (wide : Poseidon.Parameters F 6) (asset : Q) :
    ShielddNativeRnkHash.hash fq arithmetic initial square codec small wide 26 [asset] =
      block fq arithmetic initial square codec small asset := by
  unfold ShielddNativeRnkHash.hash
  simp only [List.length_cons,List.length_nil,
    if_pos (by decide : 1*256+26 < 2^64),if_pos (by decide : 1 ≤ 2)]
  simp only [ShielddNativeRnkHash.sponge,Poseidon.chunks2,List.foldl_cons,List.foldl_nil,block]

theorem block_value (small : Poseidon.Parameters F 3) (asset : Q) :
    (fq.integer (block fq arithmetic initial square codec small asset) : F) =
      Poseidon.hash3 small 26 [(fq.integer asset : F)] := by
  have permuted := ShielddNativeRnkHash.rounds_value fq arithmetic initial square codec small 65
    (ShielddNativeRnkHash.absorb fq arithmetic
      (ShielddNativeRnkHash.initialState fq arithmetic initial 3 26 1) [asset])
  rw [ShielddNativeRnkHash.absorb_value fq arithmetic,
    ShielddNativeRnkHash.initial_value fq arithmetic initial 3 26 1 (by decide)] at permuted
  have selected := congrArg (fun state : Poseidon.State F 3 => state ⟨1,by decide⟩) permuted
  simpa only [block,ShielddNativeIvkHash.fqValue,Poseidon.hash3,Poseidon.chunks2,Poseidon.sponge,
    List.map_cons,List.map_nil,List.length_cons,List.length_nil,List.foldl_cons,List.foldl_nil,
    Poseidon.permute] using selected

theorem hash_value (small : Poseidon.Parameters F 3)
    (wide : Poseidon.Parameters F 6) (asset : Q) :
    (fq.integer (ShielddNativeRnkHash.hash fq arithmetic initial square codec small wide 26 [asset]) : F) =
      Poseidon.hash3 small 26 [(fq.integer asset : F)] := by
  rw [source_callback fq arithmetic initial square codec]
  exact block_value fq arithmetic initial square codec small asset

set_option pp.all true in
#check @source_callback
#print axioms source_callback
set_option pp.all true in
#check @block_value
#print axioms block_value
set_option pp.all true in
#check @hash_value
#print axioms hash_value

end ShielddSecurity.NativeAssetHash
