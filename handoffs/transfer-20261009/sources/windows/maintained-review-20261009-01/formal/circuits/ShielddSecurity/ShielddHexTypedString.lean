import ShielddSecurity.ShielddHexSourceParameterInstance
import ShielddSecurity.ShielddJsonArtifactDispatch
import Init.Data.Char.Lemmas
import Init.Data.String.Basic

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexTypedString

/- The Artifact visitor stores String, whereas the concrete byte codec uses
List Nat. Construct the actual character sequence and prove this view seam.
This is a Lean String/character model, not a claim that an arbitrary Rust
String, UTF-8 allocation, or serde parser already refines it. -/
def fromAscii (codes : List Nat) : String :=
  String.ofList (codes.map Char.ofNat)

def view (text : String) : List Nat := text.toList.map Char.toNat

theorem ascii_char_nat (code : Nat) (ascii : code < 128) :
    (Char.ofNat code).toNat = code := by
  have valid : code.isValidChar := Or.inl (by omega)
  rw [Char.ofNat, dif_pos valid]
  rfl

theorem string_view_ascii (codes : List Nat)
    (ascii : ∀ code ∈ codes, code < 128) : view (fromAscii codes) = codes := by
  unfold view fromAscii
  rw [String.toList_ofList, List.map_map]
  have same := List.map_congr_left (l := codes)
    (f := fun code => (Char.ofNat code).toNat) (g := id)
    (fun code member => ascii_char_nat code (ascii code member))
  simpa only [Function.comp_def, List.map_id] using same

def encoded (bytes : List GroupByteCodec.Byte) : String :=
  fromAscii (ShielddHexStringOperations.encodedString bytes)

theorem encoded_string_view (bytes : List GroupByteCodec.Byte) :
    view (encoded bytes) = ShielddHexStringOperations.encodedString bytes := by
  apply string_view_ascii
  rw [ShielddHexStringOperations.hex_string_bytes]
  exact ShielddHexSourceSequence.encode_ascii bytes

def backend : ShielddNativeParameterBackend.HexBackend String where
  encode := encoded
  decode := fun text => ShielddHexSourceParameterInstance.backend.decode (view text)
  roundtrip := fun bytes => by
    change ShielddHexSourceParameterInstance.backend.decode (view (encoded bytes)) = some bytes
    rw [encoded_string_view]
    exact ShielddHexSourceParameterInstance.source_roundtrip bytes

def codec : ShielddNativeParameterBytes.HexCodec String :=
  ShielddNativeParameterBackend.hexCodec backend

theorem typed_roundtrip (bytes : List GroupByteCodec.Byte) :
    backend.decode (encoded bytes) = some bytes := backend.roundtrip bytes

theorem field_string_buffer {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (bytes : GroupByteCodec.Bytes) :
    ShielddNativeParameterBytes.fieldBody codec fq (encoded (List.ofFn bytes)) =
      fq.parse (GroupByteCodec.reverseBytes bytes) :=
  ShielddNativeParameterBackend.field_encoded_bytes backend fq bytes

/- The full Artifact matrix visitor supplies ordered typed Strings, not a
preselected field result. This composition first visits the array values and
then runs the same source decoder over every coefficient, preserving rows
and columns. Canonical Fq parsing is a separate operation after this view. -/
def decodeMatrixBytes (input : ShielddJsonArtifactDispatch.Value) :
    Option (List (List (List GroupByteCodec.Byte))) := do
  let rows ← ShielddJsonArtifactDispatch.readMatrix input
  ShielddJsonArtifactDispatch.ordered
    (ShielddJsonArtifactDispatch.ordered backend.decode) rows

theorem artifact_string_order (rows : List (List GroupByteCodec.Bytes)) :
    decodeMatrixBytes (ShielddJsonArtifactDispatch.matrixValue
      (rows.map (fun row => row.map (fun bytes => encoded (List.ofFn bytes))))) =
      some (rows.map (fun row => row.map List.ofFn)) := by
  unfold decodeMatrixBytes
  rw [ShielddJsonArtifactDispatch.ordered_matrix]
  change ShielddJsonArtifactDispatch.ordered
    (ShielddJsonArtifactDispatch.ordered backend.decode)
    (rows.map (fun row => row.map (fun bytes => encoded (List.ofFn bytes)))) = _
  have outer := ShielddJsonArtifactDispatch.ordered_success
    (ShielddJsonArtifactDispatch.ordered backend.decode)
    (fun row : List (List GroupByteCodec.Byte) => row.map encoded)
    (fun row => ShielddJsonArtifactDispatch.ordered_success backend.decode encoded
      typed_roundtrip row)
    (rows.map (fun row => row.map List.ofFn))
  simpa only [List.map_map, Function.comp_def] using outer

set_option pp.all true in
#check @ascii_char_nat
#print axioms ascii_char_nat
set_option pp.all true in
#check @string_view_ascii
#print axioms string_view_ascii
set_option pp.all true in
#check @encoded_string_view
#print axioms encoded_string_view
set_option pp.all true in
#check @typed_roundtrip
#print axioms typed_roundtrip
set_option pp.all true in
#check @field_string_buffer
#print axioms field_string_buffer
set_option pp.all true in
#check @artifact_string_order
#print axioms artifact_string_order

end ShielddSecurity.ShielddHexTypedString
