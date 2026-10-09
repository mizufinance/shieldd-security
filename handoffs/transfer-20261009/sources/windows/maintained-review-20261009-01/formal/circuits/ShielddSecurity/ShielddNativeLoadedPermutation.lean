import ShielddSecurity.ShielddNativeParameterLoader
import ShielddSecurity.ShielddNativeRnkHash

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeLoadedPermutation

open ShielddNativeParameterLoader ShielddNativeParameterBytes

/- Exact owned poseidon.rs::Permutation::load control flow. The indexed ARK
view below represents its Vec after the checked height65; the MDS view
represents its fixed square array. Serde, hex and Rust iterator/array source
instantiation remain separate obligations. No loaded coefficient or hash
result is a global primitive contract or a selected-input premise. -/

structure RecipeHeader where
  schema : String
  modulus : String
  alpha : Nat
  fullRounds : Nat
  partialRounds : Nat
  skipMatrices : Nat
  arkHeight : Nat

def sourceHeader : RecipeHeader :=
  { schema := "shieldd.poseidon381.v1",
    modulus := "52435875175126190479447740508185965837690552500527637822603658699938581184513",
    alpha := 5,
    fullRounds := 8,
    partialRounds := 57,
    skipMatrices := 0,
    arkHeight := 65 }

def recipeValid (header : RecipeHeader) : Bool :=
  header.schema == "shieldd.poseidon381.v1" && header.skipMatrices == 0 &&
  header.modulus == "52435875175126190479447740508185965837690552500527637822603658699938581184513" &&
  header.alpha == 5 && header.fullRounds == 8 && header.partialRounds == 57 &&
  header.arkHeight == 65

theorem header_guard : recipeValid sourceHeader = true := by decide

def fixedArray {Value : Type} (width : Nat) (values : List Value) :
    Option (Fin width → Value) :=
  if length : values.length = width then
    some (fun index => values.get ⟨index.val, by rw [length]; exact index.isLt⟩)
  else none

theorem fixed_array_roundtrip {Value : Type} {width : Nat} (values : Fin width → Value) :
    fixedArray width (List.ofFn values) = some values := by
  have length : (List.ofFn values).length = width := by simp
  simp only [fixedArray, dif_pos length]
  apply congrArg Option.some
  funext index
  simp only [List.get_eq_getElem, List.getElem_ofFn]

def collectRows {Index Value : Type} (load : Index → Option Value) :
    List Index → Option (List Value)
  | [] => some []
  | index :: rest => do
      let head ← load index
      let tail ← collectRows load rest
      pure (head :: tail)

theorem collect_rows_success {Index Value : Type} (load : Index → Option Value)
    (indices : List Index) (values : Index → Value)
    (successful : ∀ index ∈ indices, load index = some (values index)) :
    collectRows load indices = some (indices.map values) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    have head := successful index (List.mem_cons_self ..)
    have tail := ih (fun next member => successful next (List.mem_cons_of_mem index member))
    change (load index).bind (fun value => (collectRows load rest).bind
      (fun remaining => some (value :: remaining))) = some (values index :: rest.map values)
    rw [head, tail]
    rfl

structure NativePermutation (Q : Type) (width : Nat) where
  ark : Fin 65 → Fin width → Q
  mds : Fin width → Fin width → Q

def rowNative {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (canonical : Fin width → Nat) :
    Option (Fin width → Q) := do
  let loaded ← loadRow hex fq canonical
  fixedArray width loaded

def loadParameters {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (header : RecipeHeader)
    (ark : Fin 65 → Fin width → Nat) (mds : Fin width → Fin width → Nat) :
    Option (NativePermutation Q width) :=
  if recipeValid header then do
    let arkRows ← collectRows (fun row => rowNative hex fq (ark row))
      (List.ofFn (fun row : Fin 65 => row))
    let mdsRows ← collectRows (fun row => rowNative hex fq (mds row))
      (List.ofFn (fun row : Fin width => row))
    let indexedArk ← fixedArray 65 arkRows
    let indexedMds ← fixedArray width mdsRows
    pure { ark := indexedArk, mds := indexedMds }
  else none

theorem bad_recipe_rejected {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (header : RecipeHeader)
    (ark : Fin 65 → Fin width → Nat) (mds : Fin width → Fin width → Nat)
    (rejected : recipeValid header = false) : loadParameters hex fq header ark mds = none := by
  simp only [loadParameters, rejected, Bool.false_eq_true, if_false]

variable {F : Type} [Field F] [CharP F Scalar.modulus]

def expectedNative {Q : Type} {width : Nat} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F width) :
    NativePermutation Q width :=
  { ark := fun row column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec
      (parameters.ark row.val column),
    mds := fun row column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec
      (parameters.mds row column) }

theorem load_parameters_success {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (signed : Poseidon.Parameters Int width)
    (ark : Fin 65 → Fin width → Nat) (mds : Fin width → Fin width → Nat)
    (arkChecks : ∀ row column, ark row column < Scalar.modulus ∧
      ShielddNativePoseidonParameters.Represents (signed.ark row.val column) (ark row column))
    (mdsChecks : ∀ row column, mds row column < Scalar.modulus ∧
      ShielddNativePoseidonParameters.Represents (signed.mds row column) (mds row column)) :
    loadParameters hex fq sourceHeader ark mds =
      some (expectedNative fq arithmetic codec
        { ark := fun row column => (signed.ark row column : F),
          mds := fun row column => (signed.mds row column : F) }) := by
  let nativeArk := fun row : Fin 65 => fun column =>
    ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed.ark row.val column : F)
  let nativeMds := fun row : Fin width => fun column =>
    ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed.mds row column : F)
  have arkLoaded : collectRows (fun row => rowNative hex fq (ark row))
      (List.ofFn (fun row : Fin 65 => row)) = some (List.ofFn nativeArk) := by
    apply (collect_rows_success _ _ nativeArk ?_).trans
      (congrArg Option.some (by simp only [List.map_ofFn, Function.comp_def]))
    intro row _
    have loaded := load_row_success hex fq arithmetic codec (signed.ark row.val) (ark row)
      (arkChecks row)
    change (loadRow hex fq (ark row)).bind (fixedArray width) = some (nativeArk row)
    rw [loaded]
    change fixedArray width (List.ofFn (nativeArk row)) = some (nativeArk row)
    exact fixed_array_roundtrip _
  have mdsLoaded : collectRows (fun row => rowNative hex fq (mds row))
      (List.ofFn (fun row : Fin width => row)) = some (List.ofFn nativeMds) := by
    apply (collect_rows_success _ _ nativeMds ?_).trans
      (congrArg Option.some (by simp only [List.map_ofFn, Function.comp_def]))
    intro row _
    have loaded := load_row_success hex fq arithmetic codec (signed.mds row) (mds row)
      (mdsChecks row)
    change (loadRow hex fq (mds row)).bind (fixedArray width) = some (nativeMds row)
    rw [loaded]
    change fixedArray width (List.ofFn (nativeMds row)) = some (nativeMds row)
    exact fixed_array_roundtrip _
  unfold loadParameters
  rw [header_guard]
  simp only [if_pos rfl]
  change (collectRows (fun row => rowNative hex fq (ark row))
      (List.ofFn (fun row : Fin 65 => row))).bind (fun arkRows =>
    (collectRows (fun row => rowNative hex fq (mds row))
      (List.ofFn (fun row : Fin width => row))).bind (fun mdsRows =>
    (fixedArray 65 arkRows).bind (fun indexedArk => (fixedArray width mdsRows).bind
      (fun indexedMds => some ({ ark := indexedArk, mds := indexedMds } : NativePermutation Q width))))) = _
  rw [arkLoaded, mdsLoaded]
  change (fixedArray 65 (List.ofFn nativeArk)).bind (fun indexedArk =>
    (fixedArray width (List.ofFn nativeMds)).bind
      (fun indexedMds => some ({ ark := indexedArk, mds := indexedMds } : NativePermutation Q width))) = _
  rw [fixed_array_roundtrip, fixed_array_roundtrip]
  rfl

theorem wide_loaded {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) :
    loadParameters hex fq sourceHeader
      (fun row => RuntimeNativePoseidonParameters.wideCanonical.ark row.val)
      RuntimeNativePoseidonParameters.wideCanonical.mds =
      some (expectedNative fq arithmetic codec
        { ark := fun row column => (RuntimeHashBlock_authorization_rnk_permutation0_0.parameters.ark row column : F),
          mds := fun row column => (RuntimeHashBlock_authorization_rnk_permutation0_0.parameters.mds row column : F) }) := by
  apply load_parameters_success hex fq arithmetic codec
    RuntimeHashBlock_authorization_rnk_permutation0_0.parameters
  · intro row column
    rw [← RuntimeNativePoseidonParameters.wide_parameters]
    exact RuntimeNativePoseidonParameters.wide_ark_entries row column
  · intro row column
    rw [← RuntimeNativePoseidonParameters.wide_parameters]
    exact RuntimeNativePoseidonParameters.wide_mds_entries row column

theorem small_loaded {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) :
    loadParameters hex fq sourceHeader
      (fun row => RuntimeNativePoseidonParameters.smallCanonical.ark row.val)
      RuntimeNativePoseidonParameters.smallCanonical.mds =
      some (expectedNative fq arithmetic codec
        { ark := fun row column => (RuntimeHashBlock_authorization_rnk_permutation2_0.parameters.ark row column : F),
          mds := fun row column => (RuntimeHashBlock_authorization_rnk_permutation2_0.parameters.mds row column : F) }) := by
  apply load_parameters_success hex fq arithmetic codec
    RuntimeHashBlock_authorization_rnk_permutation2_0.parameters
  · intro row column
    rw [← RuntimeNativePoseidonParameters.small_parameters]
    exact RuntimeNativePoseidonParameters.small_ark_entries row column
  · intro row column
    rw [← RuntimeNativePoseidonParameters.small_parameters]
    exact RuntimeNativePoseidonParameters.small_mds_entries row column

/- This reads the loaded native coefficients directly, as permute does after
load. The finite ARK index comes from enumeration of the checked65 rows. -/
def nativeRound {Q : Type} {width : Nat} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (parameters : NativePermutation Q width) (index : Fin 65) (state : Poseidon.State Q width) :
    Poseidon.State Q width := fun row =>
  (List.finRange width).foldl (fun total column =>
    let shifted := arithmetic.add (state column) (parameters.ark index column)
    let transformed := if Poseidon.nonlinear index.val column.val then
      arithmetic.mul (square.square (square.square shifted)) shifted else shifted
    arithmetic.add total (arithmetic.mul (parameters.mds row column) transformed)) arithmetic.zero

theorem round_consumer {Q : Type} {width : Nat} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F width)
    (index : Fin 65) (state : Poseidon.State Q width) :
    nativeRound fq arithmetic square (expectedNative fq arithmetic codec parameters) index state =
      ShielddNativeRnkHash.round fq arithmetic square codec parameters index.val state := rfl

theorem loaded_round_consumer {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F) (signed : Poseidon.Parameters Int width)
    (ark : Fin 65 → Fin width → Nat) (mds : Fin width → Fin width → Nat)
    (arkChecks : ∀ row column, ark row column < Scalar.modulus ∧
      ShielddNativePoseidonParameters.Represents (signed.ark row.val column) (ark row column))
    (mdsChecks : ∀ row column, mds row column < Scalar.modulus ∧
      ShielddNativePoseidonParameters.Represents (signed.mds row column) (mds row column))
    (native : NativePermutation Q width)
    (loaded : loadParameters hex fq sourceHeader ark mds = some native)
    (index : Fin 65) (state : Poseidon.State Q width) :
    nativeRound fq arithmetic square native index state =
      ShielddNativeRnkHash.round fq arithmetic square codec
        { ark := fun row column => (signed.ark row column : F),
          mds := fun row column => (signed.mds row column : F) } index.val state := by
  have successful := load_parameters_success hex fq arithmetic codec signed ark mds
    arkChecks mdsChecks
  have same := Option.some.inj (successful.symm.trans loaded)
  rw [← same]
  exact round_consumer fq arithmetic square codec _ index state

set_option pp.all true in
#check @header_guard
#print axioms header_guard
set_option pp.all true in
#check @fixed_array_roundtrip
#print axioms fixed_array_roundtrip
set_option pp.all true in
#check @collect_rows_success
#print axioms collect_rows_success
set_option pp.all true in
#check @bad_recipe_rejected
#print axioms bad_recipe_rejected
set_option pp.all true in
#check @load_parameters_success
#print axioms load_parameters_success
set_option pp.all true in
#check @wide_loaded
#print axioms wide_loaded
set_option pp.all true in
#check @small_loaded
#print axioms small_loaded
set_option pp.all true in
#check @round_consumer
#print axioms round_consumer
set_option pp.all true in
#check @loaded_round_consumer
#print axioms loaded_round_consumer

end ShielddSecurity.ShielddNativeLoadedPermutation
