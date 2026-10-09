import ShielddSecurity.ReceiverLifecycle
import ShielddSecurity.ShielddNativeIvkSource

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.ShielddNativeReceiverLifecycle

/-- Pinned compliance structs.rs status tags, not an arbitrary status value. -/
inductive Status where
  | active | frozen | seized
  deriving DecidableEq

def Status.code : Status → Nat
  | .active => 1
  | .frozen => 2
  | .seized => 3

structure Leaf where
  status : Status
  generation : Fin (2^64)
  height : Fin (2^64)

def integer (leaf : Leaf) : Nat :=
  leaf.status.code + 8*leaf.generation.val + 2^67*leaf.height.val

/-- Exact validate_lifecycle branch conditions. Active leaves can retain any
u64 freeze generation; the native guard requires only zero height there. -/
def validate (leaf : Leaf) : Bool :=
  match leaf.status with
  | .active => decide (leaf.height.val = 0)
  | .frozen | .seized => decide (0 < leaf.generation.val ∧ 0 < leaf.height.val)

def activeChecked (leaf : Leaf) : Bool := decide (leaf.status = .active) && validate leaf

theorem integer_bounded (leaf : Leaf) : integer leaf < 2^131 := by
  have generation := leaf.generation.isLt
  have height := leaf.height.isLt
  have status : leaf.status.code ≤ 3 := by cases observed : leaf.status <;> simp [Status.code,observed]
  unfold integer
  norm_num at generation height ⊢
  omega

theorem active_legal (leaf : Leaf) (checked : activeChecked leaf = true) :
    ReceiverLifecycle.LegalActive (integer leaf) := by
  have both : decide (leaf.status = .active) = true ∧ validate leaf = true := by
    simpa only [activeChecked,Bool.and_eq_true] using checked
  have status : leaf.status = .active := of_decide_eq_true both.1
  have heightGuard : decide (leaf.height.val = 0) = true := by
    simpa only [validate,status] using both.2
  have height : leaf.height.val = 0 := of_decide_eq_true heightGuard
  have generation := leaf.generation.isLt
  constructor
  · simp [integer,status,Status.code,height,Nat.add_mod,Nat.mul_mod]
  · simp only [integer,status,Status.code,height,mul_zero,add_zero]
    norm_num at generation ⊢
    omega

variable {F : Type} [Field F] {Q : Type}

/-- Named universal ff::Field::pow meaning for the exact four-limb exponent
buffer used by lifecycle_field. Only exponents3/67 are instantiated below;
there is no chosen lifecycle, encoded output or row interpretation law. -/
structure PowPrimitive (fq : GroupNativeSdk.FqBytes Q) where
  pow : Q → Nat → Q
  value : ∀ base exponent, exponent < 2^64 →
    ShielddNativeIvkHash.fqValue (F := F) fq (pow base exponent) =
    (ShielddNativeIvkHash.fqValue (F := F) fq base)^exponent

def nativeField (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (power : PowPrimitive (F := F) fq) (leaf : Leaf) : Q :=
  arithmetic.add
    (arithmetic.add (initial.fromU64 leaf.status.code)
      (arithmetic.mul (power.pow (initial.fromU64 2) 3) (initial.fromU64 leaf.generation.val)))
    (arithmetic.mul (power.pow (initial.fromU64 2) 67) (initial.fromU64 leaf.height.val))

theorem native_field_value (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (power : PowPrimitive (F := F) fq) (leaf : Leaf) :
    ShielddNativeIvkHash.fqValue (F := F) fq (nativeField fq arithmetic initial power leaf) =
      (integer leaf : F) := by
  have statusBound : leaf.status.code < 2^64 := by
    cases observed : leaf.status <;> simp [Status.code,observed]
  unfold nativeField
  rw [arithmetic.addValue,arithmetic.addValue,arithmetic.mulValue,arithmetic.mulValue,
    power.value _ 3 (by decide),power.value _ 67 (by decide),initial.fromU64Value 2 (by decide),
    initial.fromU64Value leaf.status.code statusBound,
    initial.fromU64Value leaf.generation.val leaf.generation.isLt,
    initial.fromU64Value leaf.height.val leaf.height.isLt]
  simp only [integer,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  norm_num

theorem native_integer [CharP F Scalar.modulus] (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (power : PowPrimitive (F := F) fq) (leaf : Leaf) :
    fq.integer (nativeField fq arithmetic initial power leaf) = integer leaf := by
  have capacity : 2^131 < Scalar.modulus := by decide
  exact bounded_cast_injective (F := F) (fq.bounded _)
    ((integer_bounded leaf).trans capacity)
    (native_field_value fq arithmetic initial power leaf)

set_option pp.all true in
#check @integer_bounded
#print axioms integer_bounded
set_option pp.all true in
#check @active_legal
#print axioms active_legal
set_option pp.all true in
#check @native_field_value
#print axioms native_field_value
set_option pp.all true in
#check @native_integer
#print axioms native_integer

end ShielddSecurity.ShielddNativeReceiverLifecycle
