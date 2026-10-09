import ShielddSecurity.ShielddHexStringOperations
import ShielddSecurity.ShielddHexParameterInstance

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddHexSourceParameterInstance

/- The actual reviewed encode/String/byte-view and Result decode recurrences
construct the codec used by the owned field/parameter loader. No independent
hex roundtrip contract or chosen coefficient/hash result is an input. Rust
memory, full serde dispatch and compiler refinement remain separate. -/
def backend : ShielddNativeParameterBackend.HexBackend (List Nat) where
  encode := ShielddHexStringOperations.encodedString
  decode := fun encoded => ShielddHexSourceSequence.erase
    (ShielddHexSourceSequence.decode encoded)
  roundtrip := fun bytes => by
    change ShielddHexSourceSequence.erase (ShielddHexSourceSequence.decode
      (ShielddHexStringOperations.encodedString bytes)) = some bytes
    rw [ShielddHexStringOperations.hex_string_decode]
    rfl

def codec : ShielddNativeParameterBytes.HexCodec (List Nat) :=
  ShielddNativeParameterBackend.hexCodec backend

theorem source_roundtrip (bytes : List GroupByteCodec.Byte) :
    backend.decode (backend.encode bytes) = some bytes := backend.roundtrip bytes

theorem source_operations (value : Nat) (encoded : List Nat) :
    codec.render value = ShielddHexStringOperations.encodedString
      (List.ofFn (ShielddNativeParameterBytes.bigEndianBuffer value)) ∧
    codec.decode encoded = ShielddHexSourceSequence.erase
      (ShielddHexSourceSequence.decode encoded) := ⟨rfl, rfl⟩

theorem field_source_buffer {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (bytes : GroupByteCodec.Bytes) :
    ShielddNativeParameterBytes.fieldBody codec fq
      (ShielddHexStringOperations.encodedString (List.ofFn bytes)) =
      fq.parse (GroupByteCodec.reverseBytes bytes) :=
  ShielddNativeParameterBackend.field_encoded_bytes backend fq bytes

theorem asset_source_object {F Q : Type} [Field F] [CharP F Scalar.modulus]
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (canonical : TransferReduction.CanonicalField F) (asset : Q) :
    NativeAssetHashParameters.assetSource codec fq arithmetic initial square asset =
      some (NativeAssetHash.block fq arithmetic initial square canonical
        NativeAssetHashParameters.smallParameters asset) :=
  NativeAssetHashParameters.asset_source_object codec fq arithmetic initial square canonical asset

set_option pp.all true in
#check @source_roundtrip
#print axioms source_roundtrip
set_option pp.all true in
#check @source_operations
#print axioms source_operations
set_option pp.all true in
#check @field_source_buffer
#print axioms field_source_buffer
set_option pp.all true in
#check @asset_source_object
#print axioms asset_source_object

end ShielddSecurity.ShielddHexSourceParameterInstance
