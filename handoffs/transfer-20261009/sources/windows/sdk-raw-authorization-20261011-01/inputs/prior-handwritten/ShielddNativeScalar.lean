import ShielddSecurity.ShielddScalarReader

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeScalar

open GroupByteCodec

variable {F : Type} [Field F]

/-- Raw denotes valid reachable blst_fr states. Upstream closure is represented
by the operation codomains. The global contracts concern blst_fr_add/sub/mul,
blst_fr_cneg, blst_fr_inverse, blst_fr_from_uint64, the default zero and the
fixed BLST_FR_ONE representation, including the source's in-place ret==a use.
The interpretation of these upstream primitives remains explicit. -/
structure Operations (Raw : Type) where
  value : Raw → F
  defaultRaw : Raw
  oneRaw : Raw
  addRaw : Raw → Raw → Raw
  subRaw : Raw → Raw → Raw
  mulRaw : Raw → Raw → Raw
  conditionalNegRaw : Raw → Bool → Raw
  inverseRaw : Raw → Raw
  fromU64Raw : Nat → Raw
  equalRaw : Raw → Raw → Bool
  defaultValue : value defaultRaw = 0
  oneValue : value oneRaw = 1
  addMeaning : ∀ left right, value (addRaw left right) = value left + value right
  subMeaning : ∀ left right, value (subRaw left right) = value left - value right
  mulMeaning : ∀ left right, value (mulRaw left right) = value left * value right
  conditionalNegMeaning : ∀ raw flag,
    value (conditionalNegRaw raw flag) = if flag then -value raw else value raw
  inverseMeaning : ∀ raw, value raw ≠ 0 → value (inverseRaw raw) = (value raw)⁻¹
  fromU64Meaning : ∀ n : Nat, n < 2^64 → value (fromU64Raw n) = (n : F)
  zeroEquality : ∀ raw, equalRaw raw defaultRaw = true ↔ value raw = 0

/-- Exact Scalar(blst_fr) wrapper, with the raw-state invariant carried by Raw. -/
structure Wrapped (Raw : Type) where
  raw : Raw

def value {Raw : Type} (operations : Operations (F := F) Raw) (scalar : Wrapped Raw) : F :=
  operations.value scalar.raw
def zero {Raw : Type} (operations : Operations (F := F) Raw) : Wrapped Raw := ⟨operations.defaultRaw⟩
def one {Raw : Type} (operations : Operations (F := F) Raw) : Wrapped Raw := ⟨operations.oneRaw⟩
def fromU64 {Raw : Type} (operations : Operations (F := F) Raw) (n : Nat) : Wrapped Raw :=
  ⟨operations.fromU64Raw n⟩

/-- The Assign operators update the left raw state in place. Their functional
state after that call is the wrapped primitive result. The owned value-return
operators call these exact Assign wrappers and return the updated left value. -/
def addAssign {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) : Wrapped Raw :=
  ⟨operations.addRaw left.raw right.raw⟩
def subAssign {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) : Wrapped Raw :=
  ⟨operations.subRaw left.raw right.raw⟩
def mulAssign {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) : Wrapped Raw :=
  ⟨operations.mulRaw left.raw right.raw⟩
def add {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) : Wrapped Raw :=
  addAssign operations left right
def sub {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) : Wrapped Raw :=
  subAssign operations left right
def mul {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) : Wrapped Raw :=
  mulAssign operations left right
def neg {Raw : Type} (operations : Operations (F := F) Raw) (scalar : Wrapped Raw) : Wrapped Raw :=
  ⟨operations.conditionalNegRaw scalar.raw true⟩

/-- Commonware's Field::inv returns the owned zero wrapper on its explicit
zero guard, and calls the upstream inversion primitive in the other branch. -/
def inverse {Raw : Type} (operations : Operations (F := F) Raw) (scalar : Wrapped Raw) : Wrapped Raw :=
  if operations.equalRaw scalar.raw operations.defaultRaw then zero operations
  else ⟨operations.inverseRaw scalar.raw⟩

theorem zero_value {Raw : Type} (operations : Operations (F := F) Raw) :
    value operations (zero operations) = 0 := operations.defaultValue
theorem one_value {Raw : Type} (operations : Operations (F := F) Raw) :
    value operations (one operations) = 1 := operations.oneValue
theorem from_u64_value {Raw : Type} (operations : Operations (F := F) Raw)
    (n : Nat) (bounded : n < 2^64) : value operations (fromU64 operations n) = (n : F) :=
  operations.fromU64Meaning n bounded
theorem add_value {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) :
    value operations (add operations left right) = value operations left + value operations right :=
  operations.addMeaning left.raw right.raw
theorem sub_value {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) :
    value operations (sub operations left right) = value operations left - value operations right :=
  operations.subMeaning left.raw right.raw
theorem mul_value {Raw : Type} (operations : Operations (F := F) Raw) (left right : Wrapped Raw) :
    value operations (mul operations left right) = value operations left * value operations right :=
  operations.mulMeaning left.raw right.raw
theorem neg_value {Raw : Type} (operations : Operations (F := F) Raw) (scalar : Wrapped Raw) :
    value operations (neg operations scalar) = -value operations scalar :=
  operations.conditionalNegMeaning scalar.raw true
theorem inverse_value {Raw : Type} (operations : Operations (F := F) Raw) (scalar : Wrapped Raw) :
    value operations (inverse operations scalar) = (value operations scalar)⁻¹ := by
  cases checked : operations.equalRaw scalar.raw operations.defaultRaw with
  | false =>
      have nonzero : operations.value scalar.raw ≠ 0 := by
        intro equalsZero
        have impossible := (operations.zeroEquality scalar.raw).mpr equalsZero
        rw [checked] at impossible
        cases impossible
      simp only [inverse,checked,Bool.false_eq_true,ite_false,value]
      exact operations.inverseMeaning scalar.raw nonzero
  | true =>
      have equalsZero := (operations.zeroEquality scalar.raw).mp checked
      simp only [inverse,checked,ite_true,value,zero,equalsZero,inv_zero]
      exact operations.defaultValue

/-- Owned group.rs coefficient_d expression; the fixed standard coefficient
interpretation can use this derived formula rather than assume a wrapper result. -/
def coefficientD {Raw : Type} (operations : Operations (F := F) Raw) : Wrapped Raw :=
  mul operations (neg operations (fromU64 operations 10240))
    (inverse operations (fromU64 operations 10241))
theorem coefficient_d_value {Raw : Type} (operations : Operations (F := F) Raw) :
    value operations (coefficientD operations) = -(10240 : F) * (10241 : F)⁻¹ := by
  unfold coefficientD
  rw [mul_value,neg_value,inverse_value,
    from_u64_value operations 10240 (by decide),from_u64_value operations 10241 (by decide)]
  simp only [Nat.cast_ofNat]

/-- Named raw decoder primitives share the same valid-state arithmetic
interpretation. Owned Scalar wrapping and zero comparison are constructed in
readerBackend, rather than supplied as whole-reader or wrapper-result laws. -/
structure ReadPrimitives (Encoded Raw : Type) (operations : Operations (F := F) Raw) where
  fromBigEndian : Bytes → Encoded
  integer : Encoded → Nat
  rangeCheck : Encoded → Bool
  fromScalar : Encoded → Raw
  fromBigEndianCanonical : ∀ n : Nat, n < Scalar.modulus → ∀ bytes : Bytes,
    (∀ index, (bytes index).val = GroupScalarCodec.bigEndianByte n index.val) →
    integer (fromBigEndian bytes) = n
  rangeMeaning : ∀ encoded, rangeCheck encoded = true ↔ integer encoded < Scalar.modulus
  conversionMeaning : ∀ encoded, integer encoded < Scalar.modulus →
    operations.value (fromScalar encoded) = (integer encoded : F)

def readerBackend {Encoded Raw : Type} (operations : Operations (F := F) Raw)
    (primitives : ReadPrimitives Encoded Raw operations) :
    ShielddScalarReader.Backend (F := F) Encoded (Wrapped Raw) where
  fromBigEndian := primitives.fromBigEndian
  integer := primitives.integer
  rangeCheck := primitives.rangeCheck
  convert encoded := ⟨primitives.fromScalar encoded⟩
  value := value operations
  isZero scalar := operations.equalRaw scalar.raw operations.defaultRaw
  fromBigEndianCanonical := primitives.fromBigEndianCanonical
  rangeMeaning := primitives.rangeMeaning
  conversionMeaning := primitives.conversionMeaning
  zeroMeaning := fun scalar => operations.zeroEquality scalar.raw

theorem reader_value {Encoded Raw : Type} (operations : Operations (F := F) Raw)
    (primitives : ReadPrimitives Encoded Raw operations) (scalar : Wrapped Raw) :
    (readerBackend operations primitives).value scalar = value operations scalar := rfl

theorem read_allow_zero_value {Encoded Raw : Type} (operations : Operations (F := F) Raw)
    (primitives : ReadPrimitives Encoded Raw operations) (n : Nat) (bounded : n < Scalar.modulus)
    (bytes : Bytes) (canonical : ∀ index,
      (bytes index).val = GroupScalarCodec.bigEndianByte n index.val) :
    ShielddScalarReader.readCfg (readerBackend operations primitives) .allowZero bytes =
        some (⟨primitives.fromScalar (primitives.fromBigEndian bytes)⟩ : Wrapped Raw) ∧
      value operations ⟨primitives.fromScalar (primitives.fromBigEndian bytes)⟩ = (n : F) :=
  ShielddScalarReader.allow_zero_canonical (readerBackend operations primitives) n bounded bytes canonical

set_option pp.all true in
#check @zero_value
#print axioms zero_value
set_option pp.all true in
#check @one_value
#print axioms one_value
set_option pp.all true in
#check @from_u64_value
#print axioms from_u64_value
set_option pp.all true in
#check @add_value
#print axioms add_value
set_option pp.all true in
#check @sub_value
#print axioms sub_value
set_option pp.all true in
#check @mul_value
#print axioms mul_value
set_option pp.all true in
#check @neg_value
#print axioms neg_value
set_option pp.all true in
#check @inverse_value
#print axioms inverse_value
set_option pp.all true in
#check @coefficient_d_value
#print axioms coefficient_d_value
set_option pp.all true in
#check @reader_value
#print axioms reader_value
set_option pp.all true in
#check @read_allow_zero_value
#print axioms read_allow_zero_value

end ShielddSecurity.ShielddNativeScalar
