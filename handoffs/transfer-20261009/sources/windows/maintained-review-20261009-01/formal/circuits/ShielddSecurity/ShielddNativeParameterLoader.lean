import ShielddSecurity.ShielddNativeParameterBytes
import ShielddSecurity.RuntimeNativePoseidonParameters

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeParameterLoader

open ShielddNativeParameterBytes ShielddNativePoseidonParameters

/- poseidon.rs::field performs hex decoding, the exact32 check, reversal and
encoding::field. row maps that field wrapper in input order and collects errors
before checking width. The independent Option recursion below keeps that order
and failure propagation. Global hex/Fq functionality is explicit; no hash
output, selected native coefficient or Transfer consequence is a premise. -/

theorem field_body_parse {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (canonical : Nat)
    (bounded : canonical < Scalar.modulus) :
    fieldBody hex fq (hex.render canonical) = fq.parse (sourceBuffer canonical) := by
  change (hex.decode (hex.render canonical)).bind (fun bytes =>
    (fixedBuffer bytes).bind (fun buffer => fq.parse (GroupByteCodec.reverseBytes buffer))) = _
  rw [hex.canonical canonical bounded]
  change (fixedBuffer (List.ofFn (bigEndianBuffer canonical))).bind
    (fun buffer => fq.parse (GroupByteCodec.reverseBytes buffer)) = _
  rw [fixed_buffer_roundtrip]
  change fq.parse (GroupByteCodec.reverseBytes (bigEndianBuffer canonical)) = _
  rw [reversed_big_endian]

variable {F : Type} [Field F] [CharP F Scalar.modulus]

theorem coefficient_loaded {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F)
    (signed : Int) (canonical : Nat) (bounded : canonical < Scalar.modulus)
    (represented : Represents signed canonical) :
    fieldBody hex fq (hex.render canonical) =
      some (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed : F)) ∧
    fq.integer (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed : F)) = canonical := by
  have loaded : fieldBody hex fq (hex.render canonical) =
      some (ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed : F)) := by
    rw [field_body_parse hex fq canonical bounded]
    unfold ShielddNativeIvkHash.sdkConstant
    rw [coefficient_bytes codec signed canonical bounded represented]
    obtain ⟨native, parsed, _⟩ := fq.canonical canonical bounded (sourceBuffer canonical)
      (fun _ => rfl)
    rw [parsed]
    rfl
  exact ⟨loaded, field_body_integer hex fq canonical bounded _ loaded⟩

def loadValues {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) : List Encoded → Option (List Q)
  | [] => some []
  | first :: rest => do
      let head ← fieldBody hex fq first
      let tail ← loadValues hex fq rest
      pure (head :: tail)

theorem load_values_success {Index Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (indices : List Index)
    (encoded : Index → Encoded) (native : Index → Q)
    (successful : ∀ index ∈ indices, fieldBody hex fq (encoded index) = some (native index)) :
    loadValues hex fq (indices.map encoded) = some (indices.map native) := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
    have head := successful first (List.mem_cons_self ..)
    have tail := ih (fun index member => successful index (List.mem_cons_of_mem first member))
    change (fieldBody hex fq (encoded first)).bind (fun value =>
      (loadValues hex fq (rest.map encoded)).bind (fun values => some (value :: values))) =
        some (native first :: rest.map native)
    rw [head, tail]
    rfl

def loadRow {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q) (canonical : Fin width → Nat) : Option (List Q) :=
  loadValues hex fq (List.ofFn (fun column => hex.render (canonical column)))

theorem load_row_success {Encoded Q : Type} {width : Nat} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F)
    (signed : Fin width → Int) (canonical : Fin width → Nat)
    (checks : ∀ column, canonical column < Scalar.modulus ∧ Represents (signed column) (canonical column)) :
    loadRow hex fq canonical = some (List.ofFn (fun column =>
      ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed column : F))) := by
  have ordered := load_values_success hex fq (List.ofFn (fun column : Fin width => column))
    (fun column => hex.render (canonical column))
    (fun column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec (signed column : F))
    (fun column _ => (coefficient_loaded hex fq arithmetic codec (signed column) (canonical column)
      (checks column).1 (checks column).2).1)
  simpa only [List.map_ofFn, Function.comp_def, loadRow] using ordered

/- All entries below use the independent canonical SDK literal tables and the
already checked original signed Data tables. Data1 uses the same wide table by
RuntimeNativePoseidonParameters.wide_second_parameters. No per-input table
equality or desired coefficient is introduced at these applications. -/

theorem wide_ark_row {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (row : Fin 65) :
    loadRow hex fq (RuntimeNativePoseidonParameters.wideCanonical.ark row.val) =
      some (List.ofFn (fun column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec
        ((RuntimeHashBlock_authorization_rnk_permutation0_0.parameters.ark row.val column : Int) : F))) := by
  apply load_row_success
  intro column
  rw [← RuntimeNativePoseidonParameters.wide_parameters]
  exact RuntimeNativePoseidonParameters.wide_ark_entries row column

theorem wide_mds_row {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (row : Fin 6) :
    loadRow hex fq (RuntimeNativePoseidonParameters.wideCanonical.mds row) =
      some (List.ofFn (fun column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec
        ((RuntimeHashBlock_authorization_rnk_permutation0_0.parameters.mds row column : Int) : F))) := by
  apply load_row_success
  intro column
  rw [← RuntimeNativePoseidonParameters.wide_parameters]
  exact RuntimeNativePoseidonParameters.wide_mds_entries row column

theorem small_ark_row {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (row : Fin 65) :
    loadRow hex fq (RuntimeNativePoseidonParameters.smallCanonical.ark row.val) =
      some (List.ofFn (fun column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec
        ((RuntimeHashBlock_authorization_rnk_permutation2_0.parameters.ark row.val column : Int) : F))) := by
  apply load_row_success
  intro column
  rw [← RuntimeNativePoseidonParameters.small_parameters]
  exact RuntimeNativePoseidonParameters.small_ark_entries row column

theorem small_mds_row {Encoded Q : Type} (hex : HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (row : Fin 3) :
    loadRow hex fq (RuntimeNativePoseidonParameters.smallCanonical.mds row) =
      some (List.ofFn (fun column => ShielddNativeIvkHash.sdkConstant fq arithmetic codec
        ((RuntimeHashBlock_authorization_rnk_permutation2_0.parameters.mds row column : Int) : F))) := by
  apply load_row_success
  intro column
  rw [← RuntimeNativePoseidonParameters.small_parameters]
  exact RuntimeNativePoseidonParameters.small_mds_entries row column

set_option pp.all true in
#check @field_body_parse
#print axioms field_body_parse
set_option pp.all true in
#check @coefficient_loaded
#print axioms coefficient_loaded
set_option pp.all true in
#check @load_values_success
#print axioms load_values_success
set_option pp.all true in
#check @load_row_success
#print axioms load_row_success
set_option pp.all true in
#check @wide_ark_row
#print axioms wide_ark_row
set_option pp.all true in
#check @wide_mds_row
#print axioms wide_mds_row
set_option pp.all true in
#check @small_ark_row
#print axioms small_ark_row
set_option pp.all true in
#check @small_mds_row
#print axioms small_mds_row

end ShielddSecurity.ShielddNativeParameterLoader
