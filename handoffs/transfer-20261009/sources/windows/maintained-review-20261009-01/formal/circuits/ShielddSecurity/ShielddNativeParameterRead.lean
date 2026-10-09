import ShielddSecurity.ShielddNativeIvkHash

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeParameterRead

open GroupByteCodec

/-- The32-byte BE buffer obtained by decoding a canonical64-digit parameter
string. Connecting the literal JSON string to this buffer is a separate finite
artifact/source check; neither a hash nor a parser output is assumed here. -/
def bigEndian (n : Nat) : Bytes := fun index =>
  ⟨GroupScalarCodec.bigEndianByte n index.val,Nat.mod_lt _ (by decide)⟩

theorem reversed_byte (n : Nat) (index : Fin 32) :
    (reverseBytes (bigEndian n) index).val = littleEndianByte n index.val := by
  have indexBound := index.isLt
  have reverseIndex : 31-(31-index.val) = index.val := by omega
  simp only [reverseBytes,bigEndian,GroupScalarCodec.bigEndianByte,littleEndianByte]
  rw [reverseIndex]

variable {F : Type} [Field F]

/-- Exact circuit scalar-loader expression after hex::decode and its length
guard. The canonical upstream reader law derives successful AllowZero parsing;
the owned fallback is included only to make the mathematical function total. -/
def circuitParse {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (n : Nat) :
    ShielddNativeScalar.Wrapped Raw :=
  (ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations reader) .allowZero
    (bigEndian n)).getD (ShielddNativeScalar.zero operations)

theorem circuit_parse_value {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (n : Nat)
    (canonical : n < Scalar.modulus) :
    ShielddNativeScalar.value operations (circuitParse operations reader n) = (n : F) := by
  have parsed := ShielddNativeScalar.read_allow_zero_value operations reader n canonical
    (bigEndian n) (fun _ => rfl)
  unfold circuitParse
  rw [parsed.1]
  exact parsed.2

/-- Exact SDK parameter-loader byte reversal followed by the global canonical
Fq::from_bytes parser. It parses the same natural coefficient as the BE reader,
including zero; there is no per-permutation table/result premise. -/
def sdkParse {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq) (n : Nat) : Q :=
  (fq.parse (reverseBytes (bigEndian n))).getD arithmetic.zero

theorem sdk_parse_value {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq) (n : Nat)
    (canonical : n < Scalar.modulus) :
    ShielddNativeIvkHash.fqValue (F := F) fq (sdkParse fq arithmetic n) = (n : F) := by
  obtain ⟨native,parsed,integer⟩ := fq.canonical n canonical
    (reverseBytes (bigEndian n)) (reversed_byte n)
  simp only [sdkParse,parsed,Option.getD_some,ShielddNativeIvkHash.fqValue,integer]

/-- Entry-wise equality for any finite artifact table, before selecting an
ARK round or MDS row. A finite generated check supplies canonicality of every
actual stored integer; this theorem supplies both reader interpretations. -/
theorem table_values {I Raw Encoded Q : Type}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (fq : GroupNativeSdk.FqBytes Q) (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (table : I → Nat) (canonical : ∀ entry, table entry < Scalar.modulus) :
    (fun entry => ShielddNativeScalar.value operations (circuitParse operations reader (table entry))) =
      (fun entry => (table entry : F)) ∧
    (fun entry => ShielddNativeIvkHash.fqValue (F := F) fq (sdkParse fq arithmetic (table entry))) =
      (fun entry => (table entry : F)) := by
  constructor
  · funext entry
    exact circuit_parse_value operations reader (table entry) (canonical entry)
  · funext entry
    exact sdk_parse_value fq arithmetic (table entry) (canonical entry)

set_option pp.all true in
#check @reversed_byte
#print axioms reversed_byte
set_option pp.all true in
#check @circuit_parse_value
#print axioms circuit_parse_value
set_option pp.all true in
#check @sdk_parse_value
#print axioms sdk_parse_value
set_option pp.all true in
#check @table_values
#print axioms table_values

end ShielddSecurity.ShielddNativeParameterRead
