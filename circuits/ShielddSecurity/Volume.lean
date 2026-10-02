import ShielddSecurity.Arithmetic

set_option maxHeartbeats 600000
namespace ShielddSecurity
variable {F : Type} [Field F] {p : Nat} [CharP F p]

def AmountRange (bound : Nat) (value : F) : Prop :=
  ∃ n : Nat, n < bound ∧ (n : F) = value

def differenceNat (bound a b : Nat) : Nat := if a ≤ b then b-a else bound+b-a
def borrowNat (a b : Nat) : Nat := if a ≤ b then 0 else 1

theorem differenceNat_bound (bound a b : Nat) (ha : a < bound) (hb : b < bound) :
    differenceNat bound a b < bound := by
  unfold differenceNat
  split <;> omega

theorem differenceNat_equation (bound a b : Nat) (ha : a < bound) (hb : b < bound) :
    (b : F) - (a : F) = (differenceNat bound a b : F) - (borrowNat a b : F) * (bound : F) := by
  unfold differenceNat borrowNat
  split_ifs with le
  · rw [Nat.cast_sub le]
    simp
  · have subBound : a ≤ bound+b := by omega
    rw [Nat.cast_sub subBound, Nat.cast_add]
    simp
    ring

/-- The arithmetic slice only: hashes, predecessor membership, nullifiers and
the eligibility policy are separate circuit obligations. Candidate range is
unconditional, including padding. -/
structure VolumeArithmetic (bound : Nat)
    (prior outbound successor candidate limit difference useReal borrow : F) : Prop where
  priorRange : AmountRange bound prior
  outboundRange : AmountRange bound outbound
  successorRange : AmountRange bound successor
  candidateRange : AmountRange bound candidate
  limitRange : AmountRange bound limit
  differenceRange : AmountRange bound difference
  candidateEquation : prior + outbound = candidate
  successorGate : useReal * (successor - candidate) = 0
  limitGate : useReal * borrow = 0
  comparison : limit - candidate = difference - borrow * (bound : F)

/-- Every field assignment satisfying the actual arithmetic rows has bounded
integer meaning. No Rust witness-generation assumptions occur in this theorem. -/
theorem volume_arithmetic_sound (bound : Nat) (capacity : 2*bound ≤ p)
    (prior outbound successor candidate limit difference useReal borrow : F)
    (h : VolumeArithmetic bound prior outbound successor candidate limit difference useReal borrow) :
    ∃ a b s l : Nat,
      a < bound ∧ b < bound ∧ s < bound ∧ l < bound ∧
      (a : F) = prior ∧ (b : F) = outbound ∧ (s : F) = successor ∧ (l : F) = limit ∧
      a + b < bound ∧ (useReal = 1 → s = a+b ∧ s ≤ l) := by
  obtain ⟨a, ha, ea⟩ := h.priorRange
  obtain ⟨b, hb, eb⟩ := h.outboundRange
  obtain ⟨s, hs, es⟩ := h.successorRange
  obtain ⟨c, hc, ec⟩ := h.candidateRange
  obtain ⟨l, hl, el⟩ := h.limitRange
  obtain ⟨d, hd, ed⟩ := h.differenceRange
  have add : a+b = c := addition_lift (F := F) capacity ha hb hc (by
    simpa [ea, eb, ec] using h.candidateEquation)
  refine ⟨a,b,s,l,ha,hb,hs,hl,ea,eb,es,el,?_,?_⟩
  · omega
  · intro real
    have zeroBorrow : borrow = 0 := by simpa [real] using h.limitGate
    have successorEq : successor = candidate := sub_eq_zero.mp (by
      simpa [real] using h.successorGate)
    have equal : s = c := bounded_cast_injective (F := F) (p := p)
      (by omega) (by omega) (by simpa [es, ec] using successorEq)
    have comparison := comparison_lift (F := F) (p := p) (bound := bound)
      (a := c) (b := l) (difference := d) false capacity hc hl hd
      (by simpa [el, ec, ed, zeroBorrow] using h.comparison)
    have order : c ≤ l := comparison.mp rfl
    omega

#print axioms volume_arithmetic_sound
end ShielddSecurity
