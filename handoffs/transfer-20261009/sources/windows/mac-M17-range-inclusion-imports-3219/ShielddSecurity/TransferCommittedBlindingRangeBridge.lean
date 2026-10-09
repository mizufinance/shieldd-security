import ShielddSecurity.RuntimeBalanceBlindingCanonical

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferCommittedBlindingRangeBridge

/-- Actual compiled row 200768, in its captured canonical integer encoding. -/
def inputRows : List Row :=
  [⟨[(2, 1), (9, (Scalar.modulus - 1 : Nat))], []⟩]

/-- Owned blinding constraints only; full-capture inclusion is a separate contract. -/
def localRows : List Row := inputRows ++ RuntimeBalanceBlindingCanonical.originalRows

theorem checked_input : ScalarComparisonBounds.checkEquality Scalar.modulus
    inputRows [(2, 1)] [(9, 1)] = true := by decide

theorem order_lt_modulus : Scalar.order < Scalar.modulus := by decide

variable {F : Type} [Field F] [CharP F Scalar.modulus]

theorem committed_shadow (rho : Nat → F) (satisfied : Satisfies rho inputRows) :
    rho 2 = rho 9 := by
  have h := ScalarComparisonBounds.checked_equality rho inputRows satisfied
    [(2, 1)] [(9, 1)] checked_input
  simpa [eval] using h

omit [CharP F Scalar.modulus] in
theorem local_projection (rho : Nat → F) (satisfied : Satisfies rho localRows) :
    Satisfies rho inputRows ∧ Satisfies rho RuntimeBalanceBlindingCanonical.originalRows := by
  constructor
  · intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  · intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))

/-- No subgroup bound is assumed for b: it follows from the actual owned rows. -/
theorem committed_blinding_bound (rho : Nat → F) (one : rho 0 = 1)
    (four : (4 : F) ≠ 0) (satisfied : Satisfies rho localRows)
    (b : Nat) (canonical : b < Scalar.modulus) (binding : (b : F) = rho 2) :
    b < Scalar.order := by
  obtain ⟨input, owned⟩ := local_projection rho satisfied
  obtain ⟨r, bounded, represents⟩ :=
    RuntimeBalanceBlindingCanonical.actual_blinding_canonical rho one four owned
  have shadow : (r : F) = rho 9 := by
    simpa [RuntimeBalanceBlindingCanonical.privateValue, eval] using represents
  have equal : b = r := Scalar.canonical_representative_unique (rho 9) b r
    canonical (Nat.lt_trans bounded order_lt_modulus)
    (binding.trans (committed_shadow rho input)) shadow
  exact equal ▸ bounded

/-- A single global field codec supplies canonicality and representation for every value. -/
theorem decoded_committed_blinding_bound (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho localRows) : codec.decode (rho 2) < Scalar.order :=
  committed_blinding_bound rho one four satisfied (codec.decode (rho 2))
    (codec.bounded _) (codec.roundtrip _)

/-- Standard characteristic arithmetic discharges the nonzero-four gadget premise. -/
theorem four_nonzero : (4 : F) ≠ 0 := by
  intro zero
  have castZero : ((4 : Nat) : F) = ((0 : Nat) : F) := by simpa using zero
  have congruent := (CharP.cast_eq_iff_mod_eq F Scalar.modulus).mp castZero
  have small : 4 < Scalar.modulus := by decide
  have impossible : (4 : Nat) = 0 := by
    simp only [Nat.mod_eq_of_lt small, Nat.zero_mod] at congruent
    exact congruent
  omega

theorem decoded_bound (codec : TransferReduction.CanonicalField F)
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho localRows) :
    codec.decode (rho 2) < Scalar.order :=
  decoded_committed_blinding_bound codec rho one four_nonzero satisfied

/-- Global syntactic row inclusion; this module does not prove it for the full capture. -/
def FullRowInclusion (fullRows : List Row) : Prop :=
  ∀ row ∈ localRows, row ∈ fullRows

omit [CharP F Scalar.modulus] in
theorem full_projection (fullRows : List Row) (inclusion : FullRowInclusion fullRows)
    (rho : Nat → F) (satisfied : Satisfies rho fullRows) : Satisfies rho localRows := by
  intro row member
  exact satisfied row (inclusion row member)

theorem full_decoded_bound (fullRows : List Row) (inclusion : FullRowInclusion fullRows)
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho fullRows) : codec.decode (rho 2) < Scalar.order :=
  decoded_bound codec rho one (full_projection fullRows inclusion rho satisfied)

/-- The row alone permits every shadow value; it cannot supply a subgroup bound. -/
theorem input_only_complete (rho : Nat → F) (equal : rho 2 = rho 9) :
    Satisfies rho inputRows := by
  have coeff : ((Scalar.modulus - 1 : Nat) : F) = -1 := by
    have positive : 1 ≤ Scalar.modulus := by decide
    rw [Nat.cast_sub positive, CharP.cast_eq_zero F Scalar.modulus, Nat.cast_one]
    simp
  intro row member
  have identity : row = ⟨[(2, 1), (9, (Scalar.modulus - 1 : Nat))], []⟩ := by
    simpa [inputRows] using member
  subst row
  simp [eval, coeff, equal, Square]


/-- A positive copy-row assignment at the forbidden subgroup boundary. The comparator
rows, rather than this equality alone, must reject the boundary. -/
theorem input_only_order_control :
    ∃ rho : Nat → F, rho 0 = 1 ∧ Satisfies rho inputRows ∧
      (Scalar.order : F) = rho 2 ∧ Scalar.order < Scalar.modulus ∧
      ¬ Scalar.order < Scalar.order := by
  let rho : Nat → F := fun column =>
    if column = 2 ∨ column = 9 then (Scalar.order : F) else 1
  refine ⟨rho, ?_, input_only_complete rho ?_, ?_, order_lt_modulus, Nat.lt_irrefl _⟩
  · simp [rho]
  · simp [rho]
  · simp [rho]

/-- Field equality without canonical integer decoding permits a whole-modulus alias. -/
theorem noncanonical_alias_control (b : Nat) :
    ((b + Scalar.modulus : Nat) : F) = (b : F) ∧
      ¬ b + Scalar.modulus < Scalar.modulus := by
  constructor
  · simp [Nat.cast_add]
  · omega

end ShielddSecurity.TransferCommittedBlindingRangeBridge

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.checked_input
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.checked_input

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.order_lt_modulus
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.order_lt_modulus

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.committed_shadow
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.committed_shadow

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.local_projection
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.local_projection

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.committed_blinding_bound
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.committed_blinding_bound

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.decoded_committed_blinding_bound
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.decoded_committed_blinding_bound

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.four_nonzero
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.four_nonzero

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.decoded_bound
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.decoded_bound

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.full_projection
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.full_projection

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.full_decoded_bound
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.full_decoded_bound

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.input_only_complete
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.input_only_complete

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.input_only_order_control
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.input_only_order_control

set_option pp.all true in
#check @ShielddSecurity.TransferCommittedBlindingRangeBridge.noncanonical_alias_control
#print axioms ShielddSecurity.TransferCommittedBlindingRangeBridge.noncanonical_alias_control
