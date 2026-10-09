import ShielddSecurity.ShielddNativeIvkSdkProgram

set_option maxHeartbeats 350000

namespace ShielddSecurity.ShielddNativeRnkHash

variable {F : Type} [Field F] {Q : Type}
variable (fq : GroupNativeSdk.FqBytes Q)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (codec : TransferReduction.CanonicalField F)

/-- Width-polymorphic instance of the owned SDK round body. This executes the
actual square().square()*value chain, parsed ARK/MDS entries and Fq::ZERO fold.
The coefficients remain explicit data tied separately to their stored schema. -/
def transform {width : Nat} (parameters : Poseidon.Parameters F width) (index : Nat)
    (state : Poseidon.State Q width) (column : Fin width) : Q :=
  let shifted := arithmetic.add (state column)
    (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (parameters.ark index column))
  if Poseidon.nonlinear index column.val then
    arithmetic.mul (square.square (square.square shifted)) shifted else shifted

theorem transform_value {width : Nat} (parameters : Poseidon.Parameters F width) (index : Nat)
    (state : Poseidon.State Q width) (column : Fin width) :
    ShielddNativeIvkHash.fqValue (F := F) fq
        (transform fq arithmetic square codec parameters index state column) =
      let shifted := ShielddNativeIvkHash.fqValue (F := F) fq (state column) + parameters.ark index column
      if Poseidon.nonlinear index column.val then shifted^5 else shifted := by
  unfold transform
  split <;> simp_all only [arithmetic.mulValue,square.squareValue,arithmetic.addValue,
    ShielddNativeIvkHash.sdk_constant_value]
  · ring

def round {width : Nat} (parameters : Poseidon.Parameters F width) (index : Nat)
    (state : Poseidon.State Q width) : Poseidon.State Q width := fun row =>
  (List.finRange width).foldl (fun total column => arithmetic.add total
    (arithmetic.mul (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (parameters.mds row column))
      (transform fq arithmetic square codec parameters index state column))) arithmetic.zero

include initial in
theorem round_value {width : Nat} (parameters : Poseidon.Parameters F width) (index : Nat)
    (state : Poseidon.State Q width) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (round fq arithmetic square codec parameters index state column)) =
      Poseidon.round parameters index (fun column => ShielddNativeIvkHash.fqValue (F := F) fq (state column)) := by
  funext row
  have folded := Poseidon.fold_evaluates (ShielddNativeIvkHash.sdkOperations fq arithmetic codec)
    (ShielddNativeIvkHash.fqValue (F := F) fq)
    (ShielddNativeIvkHash.sdk_operations_evaluate fq arithmetic codec) (List.finRange width)
    (fun column => arithmetic.mul
      (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (parameters.mds row column))
      (transform fq arithmetic square codec parameters index state column)) arithmetic.zero
  dsimp only [ShielddNativeIvkHash.sdkOperations] at folded
  unfold round
  rw [folded]
  simp only [initial.zeroValue,arithmetic.mulValue,ShielddNativeIvkHash.sdk_constant_value,transform_value]
  rfl

def rounds {width : Nat} (parameters : Poseidon.Parameters F width) :
    Nat → Poseidon.State Q width → Poseidon.State Q width
  | 0,state => state
  | count+1,state => round fq arithmetic square codec parameters count
      (rounds parameters count state)

include initial in
theorem rounds_value {width : Nat} (parameters : Poseidon.Parameters F width)
    (count : Nat) (state : Poseidon.State Q width) :
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

def initialState (width domain arity : Nat) : Poseidon.State Q width :=
  fun column => if column.val = 0 then initial.fromU64 (arity*256+domain) else arithmetic.zero

theorem initial_value (width domain arity : Nat) (bounded : arity*256+domain < 2^64) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (initialState fq arithmetic initial width domain arity column)) = Poseidon.initial domain arity := by
  funext column
  simp only [initialState,Poseidon.initial]
  split <;> simp only [initial.fromU64Value _ bounded,initial.zeroValue]

/-- The SDK zip iterator updates only present rate lanes. Absent lanes retain
their state; this differs syntactically from adding a fabricated padding value. -/
def absorb {width : Nat} (state : Poseidon.State Q width) (chunk : List Q) : Poseidon.State Q width :=
  fun column => if column.val = 0 then state column else
    match chunk[column.val-1]? with
    | none => state column
    | some value => arithmetic.add (state column) value

theorem absorb_value {width : Nat} (state : Poseidon.State Q width) (chunk : List Q) :
    (fun column => ShielddNativeIvkHash.fqValue (F := F) fq
      (absorb fq arithmetic state chunk column)) =
      Poseidon.absorb (fun column => ShielddNativeIvkHash.fqValue (F := F) fq (state column))
        (chunk.map (ShielddNativeIvkHash.fqValue (F := F) fq)) := by
  funext column
  by_cases zero : column.val = 0
  · simp [absorb,Poseidon.absorb,zero]
  · cases read : chunk[column.val-1]? with
    | none => simp [absorb,Poseidon.absorb,zero,List.getElem?_map,read]
    | some value => simp [absorb,Poseidon.absorb,zero,List.getElem?_map,read,arithmetic.addValue]

/-- Exact two-chunk specialization of hash(domain17, nine native Fq values).
The first block absorbs five operands, the second four, with IV2321. -/
def rnk (parameters : Poseidon.Parameters F 6)
    (a b c d e f g h i : Q) : Q :=
  rounds fq arithmetic square codec parameters 65
    (absorb fq arithmetic
      (rounds fq arithmetic square codec parameters 65
        (absorb fq arithmetic (initialState fq arithmetic initial 6 17 9) [a,b,c,d,e]))
      [f,g,h,i]) ⟨1,by decide⟩

theorem rnk_value (parameters : Poseidon.Parameters F 6)
    (a b c d e f g h i : Q) :
    ShielddNativeIvkHash.fqValue (F := F) fq
      (rnk fq arithmetic initial square codec parameters a b c d e f g h i) =
      Poseidon.hash6 parameters 17
        ([a,b,c,d,e,f,g,h,i].map (ShielddNativeIvkHash.fqValue (F := F) fq)) := by
  have first := rounds_value fq arithmetic initial square codec parameters 65
    (absorb fq arithmetic (initialState fq arithmetic initial 6 17 9) [a,b,c,d,e])
  rw [absorb_value fq arithmetic,initial_value fq arithmetic initial 6 17 9 (by decide)] at first
  have second := rounds_value fq arithmetic initial square codec parameters 65
    (absorb fq arithmetic
      (rounds fq arithmetic square codec parameters 65
        (absorb fq arithmetic (initialState fq arithmetic initial 6 17 9) [a,b,c,d,e])) [f,g,h,i])
  rw [absorb_value fq arithmetic,first] at second
  have selected := congrArg (fun state : Poseidon.State F 6 => state ⟨1,by decide⟩) second
  simpa only [rnk,Poseidon.hash6,List.map_cons,List.map_nil,Poseidon.chunks5,Poseidon.sponge,
    List.length_cons,List.length_nil,List.foldl_cons,List.foldl_nil,Poseidon.permute] using selected

/-- Exact hash(domain18, singleton key): SMALL width3, rate2, IV274. -/
def commitment (parameters : Poseidon.Parameters F 3) (key : Q) : Q :=
  rounds fq arithmetic square codec parameters 65
    (absorb fq arithmetic (initialState fq arithmetic initial 3 18 1) [key]) ⟨1,by decide⟩

theorem commitment_value (parameters : Poseidon.Parameters F 3) (key : Q) :
    ShielddNativeIvkHash.fqValue (F := F) fq
      (commitment fq arithmetic initial square codec parameters key) =
      Poseidon.hash3 parameters 18 [ShielddNativeIvkHash.fqValue (F := F) fq key] := by
  have permuted := rounds_value fq arithmetic initial square codec parameters 65
    (absorb fq arithmetic (initialState fq arithmetic initial 3 18 1) [key])
  rw [absorb_value fq arithmetic,initial_value fq arithmetic initial 3 18 1 (by decide)] at permuted
  have selected := congrArg (fun state : Poseidon.State F 3 => state ⟨1,by decide⟩) permuted
  simpa only [commitment,Poseidon.hash3,Poseidon.chunks2,Poseidon.sponge,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,List.foldl_cons,List.foldl_nil,Poseidon.permute] using selected

def sponge {width : Nat} (parameters : Poseidon.Parameters F width) (domain arity : Nat)
    (chunks : List (List Q)) : Poseidon.State Q width :=
  match chunks with
  | [] => rounds fq arithmetic square codec parameters 65 (initialState fq arithmetic initial width domain arity)
  | _ :: _ => chunks.foldl (fun state chunk =>
      rounds fq arithmetic square codec parameters 65 (absorb fq arithmetic state chunk))
      (initialState fq arithmetic initial width domain arity)

/-- The owned public width selection and checked IV framing. The zero branch
totalizes native panic on an unrepresentable IV; the two callback equations
below establish that branch is unreachable for the actual RNK/commitment calls.
No arbitrary-length call is asserted to return successfully in Rust. -/
def hash (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
    (domain : Nat) (inputs : List Q) : Q :=
  if inputs.length*256+domain < 2^64 then
    if inputs.length ≤ 2 then
      sponge fq arithmetic initial square codec small domain inputs.length (Poseidon.chunks2 inputs) ⟨1,by decide⟩
    else sponge fq arithmetic initial square codec wide domain inputs.length (Poseidon.chunks5 inputs) ⟨1,by decide⟩
  else arithmetic.zero

theorem callback_rnk (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
    (a b c d e f g h i : Q) :
    hash fq arithmetic initial square codec small wide 17 [a,b,c,d,e,f,g,h,i] =
      rnk fq arithmetic initial square codec wide a b c d e f g h i := by
  unfold hash
  simp only [List.length_cons,List.length_nil,
    if_pos (by decide : 9*256+17 < 2^64),if_neg (by decide : ¬9 ≤ 2)]
  simp only [sponge,Poseidon.chunks5,List.foldl_cons,List.foldl_nil,rnk]

theorem callback_commitment (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
    (key : Q) :
    hash fq arithmetic initial square codec small wide 18 [key] =
      commitment fq arithmetic initial square codec small key := by
  unfold hash
  simp only [List.length_cons,List.length_nil,
    if_pos (by decide : 1*256+18 < 2^64),if_pos (by decide : 1 ≤ 2)]
  simp only [sponge,Poseidon.chunks2,List.foldl_cons,List.foldl_nil,commitment]

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
#check @initial_value
#print axioms initial_value
set_option pp.all true in
#check @absorb_value
#print axioms absorb_value
set_option pp.all true in
#check @rnk_value
#print axioms rnk_value
set_option pp.all true in
#check @commitment_value
#print axioms commitment_value
set_option pp.all true in
#check @callback_rnk
#print axioms callback_rnk
set_option pp.all true in
#check @callback_commitment
#print axioms callback_commitment

end ShielddSecurity.ShielddNativeRnkHash
