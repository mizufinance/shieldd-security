import ShielddSecurity.GroupByteCodec

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddScalarReader

open GroupByteCodec

variable {F : Type} [Field F]

/-- Named upstream blst/Buf primitives. The array is exactly32 bytes; the
source wrapper's [u8;SIZE] read therefore has no missing-byte branch here.
fromBigEndianCanonical is the global blst_scalar_from_bendian interpretation;
rangeMeaning is blst_scalar_fr_check; conversionMeaning is blst_fr_from_scalar.
These are upstream functional contracts, not a success or field-value law for
Shieldd's complete reader. Native equality/zero is a separate upstream law. -/
structure Backend (Encoded Native : Type) where
  fromBigEndian : Bytes → Encoded
  integer : Encoded → Nat
  rangeCheck : Encoded → Bool
  convert : Encoded → Native
  value : Native → F
  isZero : Native → Bool
  fromBigEndianCanonical : ∀ n : Nat, n < Scalar.modulus → ∀ bytes : Bytes,
    (∀ index, (bytes index).val = GroupScalarCodec.bigEndianByte n index.val) →
    integer (fromBigEndian bytes) = n
  rangeMeaning : ∀ encoded, rangeCheck encoded = true ↔ integer encoded < Scalar.modulus
  conversionMeaning : ∀ encoded, integer encoded < Scalar.modulus →
    value (convert encoded) = (integer encoded : F)
  zeroMeaning : ∀ native, isZero native = true ↔ value native = 0

inductive ReadCfg where
  | allowZero
  | rejectZero
  deriving DecidableEq

/-- Exact owned Commonware/Shieldd patched read_cfg control flow: decode,
range-check, convert, and reject zero only when RejectZero was requested.
The operations within the guard are upstream; this branch policy is owned. -/
def readCfg {Encoded Native : Type} (backend : Backend (F := F) Encoded Native)
    (cfg : ReadCfg) (bytes : Bytes) : Option Native :=
  let encoded := backend.fromBigEndian bytes
  if backend.rangeCheck encoded then
    let output := backend.convert encoded
    if cfg = .rejectZero ∧ backend.isZero output = true then none else some output
  else none

theorem allow_zero_canonical {Encoded Native : Type} (backend : Backend (F := F) Encoded Native)
    (n : Nat) (bounded : n < Scalar.modulus) (bytes : Bytes)
    (canonical : ∀ index, (bytes index).val = GroupScalarCodec.bigEndianByte n index.val) :
    readCfg backend .allowZero bytes = some (backend.convert (backend.fromBigEndian bytes)) ∧
      backend.value (backend.convert (backend.fromBigEndian bytes)) = (n : F) := by
  have decoded := backend.fromBigEndianCanonical n bounded bytes canonical
  have within : backend.integer (backend.fromBigEndian bytes) < Scalar.modulus := by
    rw [decoded]
    exact bounded
  have checked := (backend.rangeMeaning _).mpr within
  constructor
  · simp [readCfg,checked]
  · exact (backend.conversionMeaning _ within).trans (congrArg (fun n : Nat => (n : F)) decoded)

/-- The BERead instance is built from the defined AllowZero wrapper; its
canonical law is a theorem, not another assumed Shieldd reader contract. -/
def decoder {Encoded Native : Type} (backend : Backend (F := F) Encoded Native) : BERead (F := F) where
  decode bytes := (readCfg backend .allowZero bytes).map backend.value
  canonical n bounded bytes canonical := by
    have read := allow_zero_canonical backend n bounded bytes canonical
    rw [read.1]
    simp only [Option.map_some,read.2]

theorem decoder_canonical {Encoded Native : Type} (backend : Backend (F := F) Encoded Native)
    (n : Nat) (bounded : n < Scalar.modulus) (bytes : Bytes)
    (canonical : ∀ index, (bytes index).val = GroupScalarCodec.bigEndianByte n index.val) :
    (decoder backend).decode bytes = some (n : F) :=
  (decoder backend).canonical n bounded bytes canonical

theorem reject_zero_exact {Encoded Native : Type} (backend : Backend (F := F) Encoded Native)
    (bytes : Bytes) (within : backend.integer (backend.fromBigEndian bytes) < Scalar.modulus) :
    readCfg backend .rejectZero bytes = none ↔
      backend.value (backend.convert (backend.fromBigEndian bytes)) = 0 := by
  have checked := (backend.rangeMeaning _).mpr within
  cases zero : backend.isZero (backend.convert (backend.fromBigEndian bytes)) with
  | false =>
      have nonzero : backend.value (backend.convert (backend.fromBigEndian bytes)) ≠ 0 := by
        intro valueZero
        have impossible := (backend.zeroMeaning _).mpr valueZero
        rw [zero] at impossible
        cases impossible
      simp [readCfg,checked,zero,nonzero]
  | true =>
      have valueZero := (backend.zeroMeaning _).mp zero
      simp [readCfg,checked,zero,valueZero]

set_option pp.all true in
#check @allow_zero_canonical
#print axioms allow_zero_canonical
set_option pp.all true in
#check @decoder_canonical
#print axioms decoder_canonical
set_option pp.all true in
#check @reject_zero_exact
#print axioms reject_zero_exact

end ShielddSecurity.ShielddScalarReader
