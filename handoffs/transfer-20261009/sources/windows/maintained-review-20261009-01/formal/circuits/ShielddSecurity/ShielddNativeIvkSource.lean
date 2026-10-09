import ShielddSecurity.ShielddNativeIvkHash

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeIvkSource

variable {F : Type} [Field F]

/-- Exact native circuits/hash.rs initial-state writes: Scalar::zero,
Scalar::from(784), then additive absorption of the three IVK operands. This
keeps the native numeric constructors separate from the parameter reader. -/
def circuitInitial {Raw : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (nk x y : ShielddNativeScalar.Wrapped Raw) : Poseidon.State (ShielddNativeScalar.Wrapped Raw) 6 :=
  fun column => if column.val = 0 then ShielddNativeScalar.fromU64 operations 784
    else if column.val = 1 then ShielddNativeScalar.add operations (ShielddNativeScalar.zero operations) nk
    else if column.val = 2 then ShielddNativeScalar.add operations (ShielddNativeScalar.zero operations) x
    else if column.val = 3 then ShielddNativeScalar.add operations (ShielddNativeScalar.zero operations) y
    else ShielddNativeScalar.zero operations

def circuitIvk {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
    (nk x y : ShielddNativeScalar.Wrapped Raw) : ShielddNativeScalar.Wrapped Raw :=
  Poseidon.roundsOps (ShielddNativeIvkHash.circuitOperations operations reader codec) parameters 65
    (circuitInitial operations nk x y) ⟨1,by decide⟩

/-- Additional named upstream Fq::ZERO/from(u64) primitives used by the
SDK's IV and state initialization. They are global arithmetic constructors;
no particular key/hash/point output interpretation appears in this contract. -/
structure SdkInitial {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq) where
  fromU64 : Nat → Q
  zeroValue : ShielddNativeIvkHash.fqValue (F := F) fq arithmetic.zero = 0
  fromU64Value : ∀ n : Nat, n < 2^64 →
    ShielddNativeIvkHash.fqValue (F := F) fq (fromU64 n) = (n : F)

def sdkInitial {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : SdkInitial fq arithmetic) (nk x y : Q) : Poseidon.State Q 6 :=
  fun column => if column.val = 0 then initial.fromU64 784
    else if column.val = 1 then arithmetic.add arithmetic.zero nk
    else if column.val = 2 then arithmetic.add arithmetic.zero x
    else if column.val = 3 then arithmetic.add arithmetic.zero y
    else arithmetic.zero

def sdkIvk {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : SdkInitial fq arithmetic) (codec : TransferReduction.CanonicalField F)
    (parameters : Poseidon.Parameters F 6) (nk x y : Q) : Q :=
  Poseidon.roundsOps (ShielddNativeIvkHash.sdkOperations fq arithmetic codec) parameters 65
    (sdkInitial fq arithmetic initial nk x y) ⟨1,by decide⟩

private theorem from_initial {A : Type} (operations : Poseidon.Operations F A)
    (value : A → F) (laws : Poseidon.Evaluates operations value)
    (parameters : Poseidon.Parameters F 6) (state : Poseidon.State A 6) (nk x y : F)
    (initial : (fun column => value (state column)) =
      Poseidon.absorb (Poseidon.initial 16 3) [nk,x,y]) :
    value (Poseidon.roundsOps operations parameters 65 state ⟨1,by decide⟩) =
      Poseidon.hash6 parameters 16 [nk,x,y] := by
  have rounds := congrArg (fun result : Poseidon.State F 6 => result ⟨1,by decide⟩)
    (Poseidon.rounds_evaluate operations value laws parameters 65 state)
  rw [initial] at rounds
  exact rounds.trans (Poseidon.hash6_of_one_block parameters 16 [nk,x,y]
    (Poseidon.initial 16 3) (Poseidon.permute parameters (Poseidon.absorb (Poseidon.initial 16 3) [nk,x,y]))
    rfl rfl rfl)

theorem circuit_ivk_value {Raw Encoded : Type} (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
    (nk x y : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativeScalar.value operations (circuitIvk operations reader codec parameters nk x y) =
      Poseidon.hash6 parameters 16 [ShielddNativeScalar.value operations nk,
        ShielddNativeScalar.value operations x,ShielddNativeScalar.value operations y] := by
  apply from_initial _ _ (ShielddNativeIvkHash.circuit_operations_evaluate operations reader codec)
  funext column
  have alternatives : column.val = 0 ∨ column.val = 1 ∨ column.val = 2 ∨ column.val = 3 ∨
      column.val = 4 ∨ column.val = 5 := by have := column.isLt; omega
  rcases alternatives with h | h | h | h | h | h <;>
    simp [circuitInitial,Poseidon.absorb,Poseidon.initial,h,ShielddNativeScalar.add_value,
      ShielddNativeScalar.zero_value,ShielddNativeScalar.from_u64_value operations 784 (by decide)]

theorem sdk_ivk_value {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : SdkInitial fq arithmetic) (codec : TransferReduction.CanonicalField F)
    (parameters : Poseidon.Parameters F 6) (nk x y : Q) :
    ShielddNativeIvkHash.fqValue (F := F) fq (sdkIvk fq arithmetic initial codec parameters nk x y) =
      Poseidon.hash6 parameters 16 [ShielddNativeIvkHash.fqValue (F := F) fq nk,
        ShielddNativeIvkHash.fqValue (F := F) fq x,ShielddNativeIvkHash.fqValue (F := F) fq y] := by
  apply from_initial _ _ (ShielddNativeIvkHash.sdk_operations_evaluate fq arithmetic codec)
  funext column
  have alternatives : column.val = 0 ∨ column.val = 1 ∨ column.val = 2 ∨ column.val = 3 ∨
      column.val = 4 ∨ column.val = 5 := by have := column.isLt; omega
  rcases alternatives with h | h | h | h | h | h <;>
    simp [sdkInitial,Poseidon.absorb,Poseidon.initial,h,arithmetic.addValue,
      initial.zeroValue,initial.fromU64Value 784 (by decide)]

set_option pp.all true in
#check @circuit_ivk_value
#print axioms circuit_ivk_value
set_option pp.all true in
#check @sdk_ivk_value
#print axioms sdk_ivk_value

end ShielddSecurity.ShielddNativeIvkSource
