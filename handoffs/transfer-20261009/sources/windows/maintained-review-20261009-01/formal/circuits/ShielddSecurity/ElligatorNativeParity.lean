import ShielddSecurity.ElligatorNative
import ShielddSecurity.GroupByteCodec

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.ElligatorNativeParity

variable {F : Type} [Field F] [CharP F Scalar.modulus]

theorem decode_zero (codec : TransferReduction.CanonicalField F) : codec.decode 0 = 0 := by
  simpa only [Nat.cast_zero] using TransferReduction.decode_canonical_cast codec 0 (by decide)

/-- Canonical negation in the named odd prime field; extension fields are
excluded by the same explicit canonical-codec contract as the actual bit join. -/
theorem decode_neg_nonzero (codec : TransferReduction.CanonicalField F) (value : F)
    (nonzero : value ≠ 0) : codec.decode (-value) = Scalar.modulus - codec.decode value := by
  have positive : 0 < codec.decode value := by
    by_contra failure
    have zero : codec.decode value = 0 := by omega
    have roundtrip := codec.roundtrip value
    rw [zero,Nat.cast_zero] at roundtrip
    exact nonzero roundtrip.symm
  have complement : ((Scalar.modulus - codec.decode value : Nat) : F) = -value := by
    rw [Nat.cast_sub (Nat.le_of_lt (codec.bounded value)),
      CharP.cast_eq_zero F Scalar.modulus,zero_sub,codec.roundtrip]
  have canonical := TransferReduction.decode_canonical_cast codec
    (Scalar.modulus - codec.decode value) (by have := codec.bounded value; omega)
  rw [complement] at canonical
  exact canonical

/-- The native conditional sign flip is computed from its canonical parity.
It does not receive a desired circuit root, map result or parity equation. -/
def normalizeRoot (codec : TransferReduction.CanonicalField F) (choice : Bool) (root : F) : F :=
  if codec.decode root % 2 = (if choice then 1 else 0) then root else -root

theorem normalize_square (codec : TransferReduction.CanonicalField F) (choice : Bool) (root : F) :
    normalizeRoot codec choice root * normalizeRoot codec choice root = root * root := by
  by_cases same : codec.decode root % 2 = (if choice then 1 else 0)
  · simp only [normalizeRoot,if_pos same]
  · simp only [normalizeRoot,if_neg same,neg_mul_neg]

/-- Zero cannot be the true QR branch because its first cubic is nonzero.
That fact is supplied by the native square API and the independently proved
first cubic, rather than by assuming the output's required canonical parity. -/
theorem normalize_parity (codec : TransferReduction.CanonicalField F) (choice : Bool) (root : F)
    (zeroChoice : root = 0 → choice = false) :
    codec.decode (normalizeRoot codec choice root) % 2 = if choice then 1 else 0 := by
  by_cases zero : root = 0
  · have option := zeroChoice zero
    rw [zero,option]
    simp only [normalizeRoot,decode_zero,Bool.false_eq_true,if_false,Nat.zero_mod,if_true]
  · by_cases same : codec.decode root % 2 = (if choice then 1 else 0)
    · simp only [normalizeRoot,if_pos same]
      exact same
    · simp only [normalizeRoot,if_neg same,decode_neg_nonzero codec root zero]
      have bounded := codec.bounded root
      have positive : 0 < codec.decode root := by
        by_contra failure
        have decodedZero : codec.decode root = 0 := by omega
        have roundtrip := codec.roundtrip root
        rw [decodedZero,Nat.cast_zero] at roundtrip
        exact zero roundtrip.symm
      have odd : Scalar.modulus % 2 = 1 := by decide
      cases choice <;> simp only [Bool.false_eq_true,if_false,if_true] at same ⊢ <;> omega

/-- Exact circuits map.rs big-endian byte31 low-bit interpretation. Instantiating
the writer for the pinned Scalar::encode FFI remains the global byte contract. -/
theorem byte_parity (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (value : F) :
    (writer.encode value ⟨31,by decide⟩).val % 2 = codec.decode value % 2 := by
  rw [writer.byteValue]
  change GroupScalarCodec.bigEndianByte (codec.decode value) 31 % 2 = codec.decode value % 2
  have low := GroupScalarCodec.low_byte_bit (codec.decode value) 0 (by decide)
  norm_num only [Nat.pow_zero,Nat.div_one] at low
  simpa only [GroupScalarCodec.bigEndianByte,Nat.sub_self,Nat.mul_zero,
    Nat.pow_zero,Nat.div_one] using low

/-- A sqrt API's selected-square equation and the first cubic's independently
proved nonzero fact discharge the zero branch. Required parity is a conclusion
of the actual sign-flip constructor, including the exceptional zero root. -/
theorem selected_normalization (codec : TransferReduction.CanonicalField F)
    (choice : Bool) (first alternative root : F) (firstNonzero : first ≠ 0)
    (selectedSquare : root * root = if choice then first else alternative) :
    normalizeRoot codec choice root * normalizeRoot codec choice root =
      (if choice then first else alternative) ∧
    codec.decode (normalizeRoot codec choice root) % 2 = if choice then 1 else 0 := by
  refine ⟨(normalize_square codec choice root).trans selectedSquare,?_⟩
  apply normalize_parity codec choice root
  intro zero
  cases option : choice
  · rfl
  · have firstZero : (0 : F) = first := by
      simpa only [option,if_true,zero,zero_mul] using selectedSquare
    exact False.elim (firstNonzero firstZero.symm)

set_option pp.all true in
#check @decode_zero
#print axioms decode_zero
set_option pp.all true in
#check @decode_neg_nonzero
#print axioms decode_neg_nonzero
set_option pp.all true in
#check @normalize_square
#print axioms normalize_square
set_option pp.all true in
#check @normalize_parity
#print axioms normalize_parity
set_option pp.all true in
#check @byte_parity
#print axioms byte_parity
set_option pp.all true in
#check @selected_normalization
#print axioms selected_normalization

end ShielddSecurity.ElligatorNativeParity
