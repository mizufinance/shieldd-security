import ShielddSecurity.GroupNativeSdk

set_option maxHeartbeats 150000

namespace ShielddSecurity.ShielddViewingKeyAdmission

open GroupByteCodec

abbrev WideBytes := Fin 64 → Byte

/-- Exact SDK encoding.rs15-18: a zeroed64-byte buffer, with the field's
32 little-endian bytes copied into its lower half. -/
def pad (bytes : Bytes) : WideBytes := fun index =>
  if small : index.val < 32 then bytes ⟨index.val,small⟩ else 0

/-- Named upstream Jubjub Fr primitives, globally quantified over canonical
inputs. The wide decoder contract specifies the raw from_bytes_wide operation
on an arbitrary low-half canonical integer and zero high half. It does not
assume Shieldd's padding/reduce_scalar body or a chosen key's nonzero value. -/
structure Primitives {Q R : Type} (fq : GroupNativeSdk.FqBytes Q)
    (fr : GroupNativeSdk.FrBytes R) where
  fromWide : WideBytes → R
  zeroCheck : R → Bool
  wideMeaning : ∀ n : Nat, n < Scalar.modulus → ∀ bytes : WideBytes,
    (∀ index : Fin 32, (bytes ⟨index.val,by omega⟩).val = littleEndianByte n index.val) →
    (∀ index : Fin 64, 32 ≤ index.val → bytes index = 0) →
    fr.integer (fromWide bytes) = n % Scalar.order
  zeroMeaning : ∀ value, zeroCheck value = true ↔ fr.integer value = 0

variable {Q R : Type} {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}

def reduceScalar (primitives : Primitives fq fr) (hash : Q) : R :=
  primitives.fromWide (pad (fq.bytes hash))

theorem reduce_integer (primitives : Primitives fq fr) (hash : Q) :
    fr.integer (reduceScalar primitives hash) = fq.integer hash % Scalar.order := by
  unfold reduceScalar
  apply primitives.wideMeaning (fq.integer hash) (fq.bounded hash)
  · intro index
    simpa only [pad,dif_pos index.isLt] using fq.byteValue hash index
  · intro index high
    simp only [pad,dif_neg (by omega : ¬ index.val < 32)]

/-- The fallible nonzero guard in core/keys/src/keys/fvk.rs116-120. The
authorization-key identity check is an earlier independent branch. PRF-derived
OVK/DK and ka::Secret construction do not change this scalar guard. -/
def incomingScalar (primitives : Primitives fq fr) (hash : Q) : Option R :=
  let reduced := reduceScalar primitives hash
  if primitives.zeroCheck reduced then none else some reduced

theorem success_iff (primitives : Primitives fq fr) (hash : Q) :
    incomingScalar primitives hash = some (reduceScalar primitives hash) ↔
      fq.integer hash % Scalar.order ≠ 0 := by
  cases checked : primitives.zeroCheck (reduceScalar primitives hash) with
  | false =>
      have nonzero : fr.integer (reduceScalar primitives hash) ≠ 0 := by
        intro zero
        have impossible := (primitives.zeroMeaning _).mpr zero
        rw [checked] at impossible
        cases impossible
      rw [reduce_integer] at nonzero
      constructor
      · intro _
        exact nonzero
      · intro _
        simp only [incomingScalar,checked,Bool.false_eq_true,ite_false]
  | true =>
      have zero := (primitives.zeroMeaning _).mp checked
      rw [reduce_integer] at zero
      constructor
      · intro accepted
        simp only [incomingScalar,checked,ite_true] at accepted
        cases accepted
      · intro nonzero
        exact False.elim (nonzero zero)

theorem successful_scalar (primitives : Primitives fq fr) (hash : Q) (scalar : R)
    (accepted : incomingScalar primitives hash = some scalar) :
    scalar = reduceScalar primitives hash ∧ 0 < fr.integer scalar ∧ fr.integer scalar < Scalar.order := by
  cases checked : primitives.zeroCheck (reduceScalar primitives hash) with
  | false =>
      simp only [incomingScalar,checked,Bool.false_eq_true,ite_false,Option.some.injEq] at accepted
      have integerNonzero : fr.integer (reduceScalar primitives hash) ≠ 0 := by
        intro zero
        have impossible := (primitives.zeroMeaning _).mpr zero
        rw [checked] at impossible
        cases impossible
      subst scalar
      exact ⟨rfl,Nat.pos_of_ne_zero integerNonzero,fr.bounded _⟩
  | true =>
      simp only [incomingScalar,checked,ite_true] at accepted
      cases accepted

/-- Global canonical-field interpretation follows from fq.integer's bound
and the independently supplied field codec, rather than a selected IVK column
or a desired circuit denominator premise. -/
theorem accepted_field_legal {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (primitives : Primitives fq fr)
    (hash : Q) (scalar : R) (accepted : incomingScalar primitives hash = some scalar) :
    codec.decode (fq.integer hash : F) % Scalar.order ≠ 0 := by
  rw [TransferReduction.decode_canonical_cast codec _ (fq.bounded hash)]
  have scalarValue := (successful_scalar primitives hash scalar accepted).1
  have succeeds : incomingScalar primitives hash = some (reduceScalar primitives hash) := by
    simpa only [scalarValue] using accepted
  exact (success_iff primitives hash).mp succeeds

set_option pp.all true in
#check @reduce_integer
#print axioms reduce_integer
set_option pp.all true in
#check @success_iff
#print axioms success_iff
set_option pp.all true in
#check @successful_scalar
#print axioms successful_scalar
set_option pp.all true in
#check @accepted_field_legal
#print axioms accepted_field_legal

end ShielddSecurity.ShielddViewingKeyAdmission
