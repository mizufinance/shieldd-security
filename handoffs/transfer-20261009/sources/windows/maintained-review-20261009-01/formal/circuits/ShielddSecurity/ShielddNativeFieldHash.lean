import ShielddSecurity.ShielddNativeRnkHash

set_option maxHeartbeats 400000

namespace ShielddSecurity.ShielddNativeFieldHash

theorem chunks2_map {A B : Type} (f : A → B) (inputs : List A) :
    Poseidon.chunks2 (inputs.map f) = (Poseidon.chunks2 inputs).map (List.map f) := by
  cases inputs with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b tail =>
      simp only [List.map_cons, List.map_nil, Poseidon.chunks2, chunks2_map f tail]
termination_by inputs.length

theorem chunks5_map {A B : Type} (f : A → B) (inputs : List A) :
    Poseidon.chunks5 (inputs.map f) = (Poseidon.chunks5 inputs).map (List.map f) := by
  cases inputs with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => rfl
      | cons c rest =>
        cases rest with
        | nil => rfl
        | cons d rest =>
          cases rest with
          | nil => rfl
          | cons e tail =>
            simp only [List.map_cons, List.map_nil, Poseidon.chunks5, chunks5_map f tail]
termination_by inputs.length

variable {F : Type} [Field F] {Q : Type}
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

include initial in
/-- Symbolic composition of the SDK's actual additive absorption and 65 rounds.
No per-call output, row assignment, or native hash value is a premise. -/
theorem fold_value {width : Nat} (parameters : Poseidon.Parameters F width)
    (chunks : List (List Q)) (state : Poseidon.State Q width) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (chunks.foldl (fun current chunk =>
        ShielddNativeRnkHash.rounds fq arithmetic square codec parameters 65
          (ShielddNativeRnkHash.absorb fq arithmetic current chunk)) state column)) =
      (chunks.map (List.map (ShielddNativeIvkHash.fqValue (F := F) fq))).foldl
        (fun current chunk => Poseidon.permute parameters (Poseidon.absorb current chunk))
        (fun column => ShielddNativeIvkHash.fqValue (F := F) fq (state column)) := by
  induction chunks generalizing state with
  | nil => rfl
  | cons head tail ih =>
    simpa only [List.foldl_cons, List.map_cons, Poseidon.permute,
      ShielddNativeRnkHash.rounds_value fq arithmetic initial square codec,
      ShielddNativeRnkHash.absorb_value fq arithmetic] using
        ih (ShielddNativeRnkHash.rounds fq arithmetic square codec parameters 65
          (ShielddNativeRnkHash.absorb fq arithmetic state head))

/-- The empty-input branch performs one permutation; other inputs use the
symbolic fold. The IV bound is the SDK from-u64 precondition. -/
theorem sponge_value {width : Nat} (parameters : Poseidon.Parameters F width)
    (domain arity : Nat) (chunks : List (List Q))
    (bounded : arity * 256 + domain < 2^64) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (ShielddNativeRnkHash.sponge fq arithmetic initial square codec parameters
        domain arity chunks column)) =
      Poseidon.sponge parameters domain arity
        (chunks.map (List.map (ShielddNativeIvkHash.fqValue (F := F) fq))) := by
  cases chunks with
  | nil =>
    simpa only [ShielddNativeRnkHash.sponge, Poseidon.sponge, List.map_nil,
      Poseidon.permute, ShielddNativeRnkHash.initial_value fq arithmetic initial
        width domain arity bounded] using
      ShielddNativeRnkHash.rounds_value fq arithmetic initial square codec parameters 65
        (ShielddNativeRnkHash.initialState fq arithmetic initial width domain arity)
  | cons head tail =>
    simpa only [ShielddNativeRnkHash.sponge, Poseidon.sponge, List.map_cons,
      ShielddNativeRnkHash.initial_value fq arithmetic initial width domain arity bounded] using
      fold_value fq arithmetic initial square codec parameters (head :: tail)
        (ShielddNativeRnkHash.initialState fq arithmetic initial width domain arity)

/-- The same SDK hash callback covers both width choices and any finite input
length with a representable IV, including the 64-field Transfer statement.
Parameter bytes and actual caller operands are separate source obligations. -/
theorem hash_value (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
    (domain : Nat) (inputs : List Q) (bounded : inputs.length * 256 + domain < 2^64) :
    ShielddNativeIvkHash.fqValue (F := F) fq
      (ShielddNativeRnkHash.hash fq arithmetic initial square codec small wide domain inputs) =
      Poseidon.hash small wide domain
        (inputs.map (ShielddNativeIvkHash.fqValue (F := F) fq)) := by
  unfold ShielddNativeRnkHash.hash Poseidon.hash
  rw [if_pos bounded]
  simp only [List.length_map]
  by_cases short : inputs.length ≤ 2
  · rw [if_pos short, if_pos short]
    have result := congrArg (fun state : Poseidon.State F 3 => state ⟨1, by decide⟩)
      (sponge_value fq arithmetic initial square codec small domain inputs.length
        (Poseidon.chunks2 inputs) bounded)
    rw [← chunks2_map] at result
    simpa only [Poseidon.hash3, List.length_map] using result
  · rw [if_neg short, if_neg short]
    have result := congrArg (fun state : Poseidon.State F 6 => state ⟨1, by decide⟩)
      (sponge_value fq arithmetic initial square codec wide domain inputs.length
        (Poseidon.chunks5 inputs) bounded)
    rw [← chunks5_map] at result
    simpa only [Poseidon.hash6, List.length_map] using result

set_option pp.all true in
#check @chunks2_map
#print axioms chunks2_map
set_option pp.all true in
#check @chunks5_map
#print axioms chunks5_map
set_option pp.all true in
#check @fold_value
#print axioms fold_value
set_option pp.all true in
#check @sponge_value
#print axioms sponge_value
set_option pp.all true in
#check @hash_value
#print axioms hash_value

end ShielddSecurity.ShielddNativeFieldHash
