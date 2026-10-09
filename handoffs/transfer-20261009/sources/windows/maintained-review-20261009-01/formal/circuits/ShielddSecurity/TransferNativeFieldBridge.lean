import ShielddSecurity.ShielddNativeEncode
import ShielddSecurity.TransferStatement

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferNativeFieldBridge

variable {F Sdk Raw Encoded Written : Type} [Field F] [CharP F Scalar.modulus]

/-! Direct semantics of the owned encoding.rs field/native_field wrappers.
The standard SDK Fq byte codec and named BLST primitives remain global
functional contracts. Success and field meaning of Shieldd's wrappers are
derived from their defined reverse/read/encode bodies. Native source argument
interpretation is tracked separately by statement_projection's source guards;
no compiled rows, desired hash value or Transfer poststate is supplied here. -/

structure SdkEncoder (Sdk F : Type) [Field F] where
  value : Sdk → F
  integer : Sdk → Nat
  toBytes : Sdk → GroupByteCodec.Bytes
  integerBounded : ∀ input, integer input < Scalar.modulus
  integerValue : ∀ input, (integer input : F) = value input
  byteMeaning : ∀ input index,
    (toBytes input index).val = GroupByteCodec.littleEndianByte (integer input) index.val

structure SdkDecoder (Sdk F : Type) [Field F] where
  value : Sdk → F
  fromBytes : GroupByteCodec.Bytes → Option Sdk
  canonical : ∀ n : Nat, n < Scalar.modulus → ∀ bytes : GroupByteCodec.Bytes,
    (∀ index, (bytes index).val = GroupByteCodec.littleEndianByte n index.val) →
    ∃ output, fromBytes bytes = some output ∧ value output = (n : F)

def field (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) (input : Sdk) : Option (ShielddNativeScalar.Wrapped Raw) :=
  ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations primitives)
    .allowZero (GroupByteCodec.reverseBytes (sdk.toBytes input))

theorem field_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) (input : Sdk) :
    (field operations primitives sdk input).map (ShielddNativeScalar.value operations) = some (sdk.value input) := by
  change (ShielddScalarReader.decoder (ShielddNativeScalar.readerBackend operations primitives)).decode
    (GroupByteCodec.reverseBytes (sdk.toBytes input)) = _
  have read := GroupByteCodec.reversed_coordinate_read
    (ShielddScalarReader.decoder (ShielddNativeScalar.readerBackend operations primitives))
    (sdk.integer input) (sdk.integerBounded input) (sdk.toBytes input) (sdk.byteMeaning input)
  simpa only [sdk.integerValue input] using read

theorem field_success (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) (input : Sdk) :
    ∃ output, field operations primitives sdk input = some output ∧
      ShielddNativeScalar.value operations output = sdk.value input := by
  have meaning := field_value operations primitives sdk input
  cases checked : field operations primitives sdk input with
  | none => simp only [checked, Option.map_none] at meaning; cases meaning
  | some output =>
      refine ⟨output, by simp only [checked], ?_⟩
      simpa only [checked, Option.map_some, Option.some.injEq] using meaning

def nativeField (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (sdk : SdkDecoder Sdk F) (input : ShielddNativeScalar.Wrapped Raw) : Option Sdk :=
  sdk.fromBytes (GroupByteCodec.reverseBytes (ShielddNativeEncode.encode operations primitives input))

theorem native_field_success (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (codec : TransferReduction.CanonicalField F) (sdk : SdkDecoder Sdk F)
    (input : ShielddNativeScalar.Wrapped Raw) :
    ∃ output, nativeField operations primitives sdk input = some output ∧
      sdk.value output = ShielddNativeScalar.value operations input := by
  have bytes : ∀ index : Fin 32,
      ((GroupByteCodec.reverseBytes (ShielddNativeEncode.encode operations primitives input)) index).val =
        GroupByteCodec.littleEndianByte (codec.decode (ShielddNativeScalar.value operations input)) index.val := by
    intro index
    dsimp only [GroupByteCodec.reverseBytes]
    rw [ShielddNativeEncode.byte_value operations primitives codec]
    have mirror : 31 - (31 - index.val) = index.val := by have := index.isLt; omega
    simp only [GroupScalarCodec.bigEndianByte, GroupByteCodec.littleEndianByte, mirror]
  obtain ⟨output, read, meaning⟩ := sdk.canonical
    (codec.decode (ShielddNativeScalar.value operations input)) (codec.bounded _)
    (GroupByteCodec.reverseBytes (ShielddNativeEncode.encode operations primitives input)) bytes
  exact ⟨output, read, meaning.trans (codec.roundtrip _)⟩

def fields (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) : List Sdk → Option (List (ShielddNativeScalar.Wrapped Raw))
  | [] => some []
  | input :: rest => (field operations primitives sdk input).bind fun output =>
      (fields operations primitives sdk rest).map (List.cons output)

theorem fields_success (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) (inputs : List Sdk) :
    ∃ outputs, fields operations primitives sdk inputs = some outputs ∧
      outputs.map (ShielddNativeScalar.value operations) = inputs.map sdk.value ∧
      outputs.length = inputs.length := by
  induction inputs with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons input rest ih =>
      obtain ⟨output, read, meaning⟩ := field_success operations primitives sdk input
      obtain ⟨outputs, reads, meanings, count⟩ := ih
      refine ⟨output :: outputs, ?_, ?_, ?_⟩
      · simp only [fields, read, Option.bind_some, reads, Option.map_some]
      · simp only [List.map_cons, meaning, meanings]
      · simp only [List.length_cons, count]

theorem statement_full64_conversion (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) (statement : TransferStatement Sdk) :
    ∃ outputs, fields operations primitives sdk statement.fields = some outputs ∧
      outputs.map (ShielddNativeScalar.value operations) = statement.fields.map sdk.value ∧ outputs.length = 64 := by
  obtain ⟨outputs, read, meaning, count⟩ := fields_success operations primitives sdk statement.fields
  exact ⟨outputs, read, meaning, count.trans (TransferStatement.fields_length _)⟩

/-- A native Poseidon result is an SDK field value. Its Scalar conversion
preserves that value for every input result, without a hash-injectivity law or
an assumed match to a desired compiled hash/statement. -/
theorem statement_hash_conversion (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : SdkEncoder Sdk F) (nativeHash : List Sdk → Sdk) (statement : TransferStatement Sdk) :
    ∃ output, field operations primitives sdk (nativeHash statement.fields) = some output ∧
      ShielddNativeScalar.value operations output = sdk.value (nativeHash statement.fields) :=
  field_success operations primitives sdk (nativeHash statement.fields)

set_option pp.all true in
#check @field_value
#print axioms field_value
set_option pp.all true in
#check @field_success
#print axioms field_success
set_option pp.all true in
#check @native_field_success
#print axioms native_field_success
set_option pp.all true in
#check @fields_success
#print axioms fields_success
set_option pp.all true in
#check @statement_full64_conversion
#print axioms statement_full64_conversion
set_option pp.all true in
#check @statement_hash_conversion
#print axioms statement_hash_conversion

end ShielddSecurity.TransferNativeFieldBridge
