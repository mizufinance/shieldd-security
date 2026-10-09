import ShielddSecurity.ShielddNativeScalar
import ShielddSecurity.GroupNativeSdk
import ShielddSecurity.Poseidon

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeIvkHash

open GroupByteCodec

variable {F : Type} [Field F]

/-- The owned circuit parameter loader uses Scalar::read_cfg AllowZero on
canonical BE coefficients. Its default fallback is unreachable by the codec
and the globally interpreted primitive reader. -/
def circuitConstant {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (codec : TransferReduction.CanonicalField F)
    (coefficient : F) : ShielddNativeScalar.Wrapped Raw :=
  (ShielddScalarReader.readCfg (ShielddNativeScalar.readerBackend operations reader) .allowZero
    ((canonicalWrite codec).encode coefficient)).getD (ShielddNativeScalar.zero operations)

theorem circuit_constant_value {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (codec : TransferReduction.CanonicalField F)
    (coefficient : F) : ShielddNativeScalar.value operations (circuitConstant operations reader codec coefficient) = coefficient := by
  have decoded := ShielddScalarReader.allow_zero_canonical (ShielddNativeScalar.readerBackend operations reader)
    (codec.decode coefficient) (codec.bounded coefficient) ((canonicalWrite codec).encode coefficient)
    ((canonicalWrite codec).byteValue coefficient)
  unfold circuitConstant
  rw [decoded.1]
  exact decoded.2.trans (codec.roundtrip coefficient)

def circuitOperations {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (codec : TransferReduction.CanonicalField F) :
    Poseidon.Operations F (ShielddNativeScalar.Wrapped Raw) :=
  ⟨circuitConstant operations reader codec,ShielddNativeScalar.add operations,ShielddNativeScalar.mul operations⟩

theorem circuit_operations_evaluate {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations) (codec : TransferReduction.CanonicalField F) :
    Poseidon.Evaluates (circuitOperations operations reader codec) (ShielddNativeScalar.value operations) :=
  ⟨circuit_constant_value operations reader codec,ShielddNativeScalar.add_value operations,ShielddNativeScalar.mul_value operations⟩

def fqValue {Q : Type} (fq : GroupNativeSdk.FqBytes Q) (value : Q) : F := (fq.integer value : F)

/-- Global upstream Jubjub Fq addition/multiplication interpretation. Native
parameter parsing and the Shieldd round/hash bodies are defined separately;
this record contains no whole-permutation or chosen-hash-result contract. -/
structure FqArithmetic (Q : Type) (fq : GroupNativeSdk.FqBytes Q) where
  zero : Q
  add : Q → Q → Q
  mul : Q → Q → Q
  addValue : ∀ left right, fqValue (F := F) fq (add left right) = fqValue (F := F) fq left + fqValue (F := F) fq right
  mulValue : ∀ left right, fqValue (F := F) fq (mul left right) = fqValue (F := F) fq left * fqValue (F := F) fq right

def littleEndianWrite (codec : TransferReduction.CanonicalField F) (coefficient : F) : Bytes :=
  fun index => ⟨littleEndianByte (codec.decode coefficient) index.val,Nat.mod_lt _ (by decide)⟩

/-- SDK parameter strings are canonical BE hex reversed before Fq::from_bytes.
The LE byte buffer here is precisely that canonical parsed coefficient view;
matching each stored ARK/MDS entry to the pinned artifacts remains explicit. -/
def sdkConstant {Q : Type} (fq : GroupNativeSdk.FqBytes Q) (arithmetic : FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (coefficient : F) : Q :=
  (fq.parse (littleEndianWrite codec coefficient)).getD arithmetic.zero

theorem sdk_constant_value {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : FqArithmetic (F := F) Q fq) (codec : TransferReduction.CanonicalField F) (coefficient : F) :
    fqValue (F := F) fq (sdkConstant fq arithmetic codec coefficient) = coefficient := by
  obtain ⟨native,parsed,integer⟩ := fq.canonical (codec.decode coefficient) (codec.bounded coefficient)
    (littleEndianWrite codec coefficient) (fun _ => rfl)
  simp only [sdkConstant,parsed,Option.getD_some,fqValue,integer]
  exact codec.roundtrip coefficient

def sdkOperations {Q : Type} (fq : GroupNativeSdk.FqBytes Q) (arithmetic : FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) : Poseidon.Operations F Q :=
  ⟨sdkConstant fq arithmetic codec,arithmetic.add,arithmetic.mul⟩

theorem sdk_operations_evaluate {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : FqArithmetic (F := F) Q fq) (codec : TransferReduction.CanonicalField F) :
    Poseidon.Evaluates (sdkOperations fq arithmetic codec) (fqValue (F := F) fq) :=
  ⟨sdk_constant_value fq arithmetic codec,arithmetic.addValue,arithmetic.mulValue⟩

/-- Exact IVK arity3/domain16 source specialization of both native hash
bodies. The IV is784, rate5 absorbs NK/AK.x/AK.y into lanes1/2/3 once, and
the existing symbolic65-round recurrence supplies both fifth chains and MDS
folds. This source expression never substitutes an assumed hash output. -/
def initialState {A : Type} (operations : Poseidon.Operations F A) (nk x y : A) : Poseidon.State A 6 :=
  fun column => if column.val = 0 then operations.constant 784
    else if column.val = 1 then operations.add (operations.constant 0) nk
    else if column.val = 2 then operations.add (operations.constant 0) x
    else if column.val = 3 then operations.add (operations.constant 0) y
    else operations.constant 0

def nativeIvk {A : Type} (operations : Poseidon.Operations F A) (parameters : Poseidon.Parameters F 6)
    (nk x y : A) : A :=
  Poseidon.roundsOps operations parameters 65 (initialState operations nk x y) ⟨1,by decide⟩

theorem native_ivk_evaluate {A : Type} (operations : Poseidon.Operations F A) (value : A → F)
    (laws : Poseidon.Evaluates operations value) (parameters : Poseidon.Parameters F 6) (nk x y : A) :
    value (nativeIvk operations parameters nk x y) =
      Poseidon.hash6 parameters 16 [value nk,value x,value y] := by
  have initial : (fun column => value (initialState operations nk x y column)) =
      Poseidon.absorb (Poseidon.initial 16 3) [value nk,value x,value y] := by
    funext column
    have alternatives : column.val = 0 ∨ column.val = 1 ∨ column.val = 2 ∨ column.val = 3 ∨
        column.val = 4 ∨ column.val = 5 := by have := column.isLt; omega
    rcases alternatives with h | h | h | h | h | h <;>
      simp [initialState,Poseidon.absorb,Poseidon.initial,h,laws.constant,laws.add]
  have rounds := congrArg (fun state : Poseidon.State F 6 => state ⟨1,by decide⟩)
    (Poseidon.rounds_evaluate operations value laws parameters 65 (initialState operations nk x y))
  rw [initial] at rounds
  exact rounds.trans (Poseidon.hash6_of_one_block parameters 16 [value nk,value x,value y]
    (Poseidon.initial 16 3) (Poseidon.permute parameters
      (Poseidon.absorb (Poseidon.initial 16 3) [value nk,value x,value y])) rfl rfl rfl)

set_option pp.all true in
#check @circuit_constant_value
#print axioms circuit_constant_value
set_option pp.all true in
#check @circuit_operations_evaluate
#print axioms circuit_operations_evaluate
set_option pp.all true in
#check @sdk_constant_value
#print axioms sdk_constant_value
set_option pp.all true in
#check @sdk_operations_evaluate
#print axioms sdk_operations_evaluate
set_option pp.all true in
#check @native_ivk_evaluate
#print axioms native_ivk_evaluate

end ShielddSecurity.ShielddNativeIvkHash
