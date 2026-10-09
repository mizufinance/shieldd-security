import ShielddSecurity.ShielddHexTypedString
import ShielddSecurity.ShielddNativeLoadedPermutation

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddHexArtifactLoader

open ShielddJsonArtifactDispatch ShielddNativeLoadedPermutation

/- Actual owned Permutation::load takes the Artifact's String matrices and
maps field, ordered Result collection and fixed-array conversion. This
independent sequence keeps those arguments, instead of replacing them with
an assumed decoded coefficient table. Result payloads are erased to Option.
The JSON parser/borrow memory and Rust compiler correspondence remain open. -/
def header (artifact : Artifact) : RecipeHeader :=
  { schema := artifact.schema, modulus := artifact.modulus, alpha := artifact.alpha, fullRounds := artifact.fullRounds, partialRounds := artifact.partialRounds, skipMatrices := artifact.skipMatrices, arkHeight := artifact.ark.length }

def fieldRow {Q : Type} (width : Nat) (fq : GroupNativeSdk.FqBytes Q)
    (strings : List String) : Option (Fin width → Q) := do
  let values ← ordered (ShielddNativeParameterBytes.fieldBody ShielddHexTypedString.codec fq) strings
  fixedArray width values

def loadArtifact {Q : Type} (width : Nat) (fq : GroupNativeSdk.FqBytes Q)
    (artifact : Artifact) : Option (NativePermutation Q width) :=
  if recipeValid (header artifact) then do
    let arkRows ← ordered (fieldRow width fq) artifact.ark
    let mdsRows ← ordered (fieldRow width fq) artifact.mds
    let indexedArk ← fixedArray 65 arkRows
    let indexedMds ← fixedArray width mdsRows
    pure ({ ark := indexedArk, mds := indexedMds } : NativePermutation Q width)
  else none

theorem ordered_field_loop {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (strings : List String) :
    ordered (ShielddNativeParameterBytes.fieldBody ShielddHexTypedString.codec fq) strings =
      ShielddNativeParameterLoader.loadValues ShielddHexTypedString.codec fq strings := by
  induction strings with
  | nil => rfl
  | cons first rest ih =>
    change (ShielddNativeParameterBytes.fieldBody ShielddHexTypedString.codec fq first).bind
      (fun head => (ordered (ShielddNativeParameterBytes.fieldBody ShielddHexTypedString.codec fq) rest).bind
        (fun tail => some (head :: tail))) =
      (ShielddNativeParameterBytes.fieldBody ShielddHexTypedString.codec fq first).bind
        (fun head => (ShielddNativeParameterLoader.loadValues ShielddHexTypedString.codec fq rest).bind
          (fun tail => some (head :: tail)))
    rw [ih]

theorem ordered_iterator {A B C : Type} (load : B → Option C) (encode : A → B)
    (indices : List A) :
    ordered load (indices.map encode) =
      collectRows (fun index => load (encode index)) indices := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
    change (load (encode first)).bind (fun head =>
      (ordered load (rest.map encode)).bind (fun tail => some (head :: tail))) =
      (load (encode first)).bind (fun head =>
        (collectRows (fun index => load (encode index)) rest).bind
          (fun tail => some (head :: tail)))
    rw [ih]

def renderRow {width : Nat} (canonical : Fin width → Nat) : List String :=
  List.ofFn (fun column => ShielddHexTypedString.codec.render (canonical column))

def sourceArtifact {width : Nat} (ark : Fin 65 → Fin width → Nat)
    (mds : Fin width → Fin width → Nat) : Artifact :=
  { schema := sourceHeader.schema, modulus := sourceHeader.modulus, alpha := sourceHeader.alpha, fullRounds := sourceHeader.fullRounds, partialRounds := sourceHeader.partialRounds, skipMatrices := sourceHeader.skipMatrices, ark := (List.ofFn (fun row : Fin 65 => row)).map (fun row => renderRow (ark row)), mds := (List.ofFn (fun row : Fin width => row)).map (fun row => renderRow (mds row)) }

theorem source_header {width : Nat} (ark : Fin 65 → Fin width → Nat)
    (mds : Fin width → Fin width → Nat) :
    header (sourceArtifact ark mds) = sourceHeader := by
  simp only [header, sourceArtifact, sourceHeader, List.length_map, List.length_ofFn]

private theorem rendered_row {Q : Type} {width : Nat} (fq : GroupNativeSdk.FqBytes Q)
    (canonical : Fin width → Nat) :
    fieldRow width fq (renderRow canonical) =
      rowNative ShielddHexTypedString.codec fq canonical := by
  unfold fieldRow
  rw [ordered_field_loop]
  rfl

theorem artifact_loader_sequence {Q : Type} {width : Nat} (fq : GroupNativeSdk.FqBytes Q)
    (ark : Fin 65 → Fin width → Nat) (mds : Fin width → Fin width → Nat) :
    loadArtifact width fq (sourceArtifact ark mds) =
      loadParameters ShielddHexTypedString.codec fq sourceHeader ark mds := by
  unfold loadArtifact
  rw [source_header]
  simp only [sourceArtifact, ordered_iterator, rendered_row]
  rfl

variable {F : Type} [Field F] [CharP F Scalar.modulus]

theorem small_source_object {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (canonical : TransferReduction.CanonicalField F) :
    loadArtifact 3 fq (sourceArtifact
      (fun row => RuntimeNativePoseidonParameters.smallCanonical.ark row.val)
      RuntimeNativePoseidonParameters.smallCanonical.mds) =
      some (expectedNative fq arithmetic canonical
        { ark := fun row column => (RuntimeHashBlock_authorization_rnk_permutation2_0.parameters.ark row column : F), mds := fun row column => (RuntimeHashBlock_authorization_rnk_permutation2_0.parameters.mds row column : F) }) := by
  rw [artifact_loader_sequence]
  exact small_loaded ShielddHexTypedString.codec fq arithmetic canonical

theorem wide_source_object {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (canonical : TransferReduction.CanonicalField F) :
    loadArtifact 6 fq (sourceArtifact
      (fun row => RuntimeNativePoseidonParameters.wideCanonical.ark row.val)
      RuntimeNativePoseidonParameters.wideCanonical.mds) =
      some (expectedNative fq arithmetic canonical
        { ark := fun row column => (RuntimeHashBlock_authorization_rnk_permutation0_0.parameters.ark row column : F), mds := fun row column => (RuntimeHashBlock_authorization_rnk_permutation0_0.parameters.mds row column : F) }) := by
  rw [artifact_loader_sequence]
  exact wide_loaded ShielddHexTypedString.codec fq arithmetic canonical

set_option pp.all true in
#check @ordered_field_loop
#print axioms ordered_field_loop
set_option pp.all true in
#check @ordered_iterator
#print axioms ordered_iterator
set_option pp.all true in
#check @source_header
#print axioms source_header
set_option pp.all true in
#check @artifact_loader_sequence
#print axioms artifact_loader_sequence
set_option pp.all true in
#check @small_source_object
#print axioms small_source_object
set_option pp.all true in
#check @wide_source_object
#print axioms wide_source_object

end ShielddSecurity.ShielddHexArtifactLoader
