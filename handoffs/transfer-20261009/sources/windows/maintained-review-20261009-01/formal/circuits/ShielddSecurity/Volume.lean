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

/-- The native caller asserts that context minus one is Boolean. This derives
the two context values from that field constraint; it does not assume either
branch and does not bind the argument to an observed runtime column. -/
theorem volume_context_cases (context : F)
    (boolean : (context - 1) * (context - 1) = context - 1) :
    context = 1 ∨ context = 2 := by
  have factor : (context - 1) * (context - 2) =
      (context - 1) * (context - 1) - (context - 1) := by ring
  have zero : (context - 1) * (context - 2) = 0 := by
    rw [factor, boolean, sub_self]
  rcases mul_eq_zero.mp zero with ordinary | fee
  · exact Or.inl (sub_eq_zero.mp ordinary)
  · exact Or.inr (sub_eq_zero.mp fee)

/-- Transfer's extra context/external product forces ordinary context for a
nonzero external flag. Native address equality, the actual flag's Boolean
construction and its compiled product/assertion certificates are separate. -/
theorem volume_external_requires_ordinary (context externalFlag : F)
    (nonzero : externalFlag ≠ 0)
    (gate : (context - 1) * externalFlag = 0) : context = 1 := by
  exact sub_eq_zero.mp ((mul_eq_zero.mp gate).resolve_right nonzero)

/-- The actual 64/48/17-bit timestamp equation has unambiguous integer meaning.
Range decompositions and the linear row must supply these premises on the same
assignment. No native witness-generation or desired day decomposition is assumed.
The stronger source bound second ≤86399 is an additional comparator obligation. -/
theorem volume_timestamp_lift (capacity : 2 ^ 65 ≤ p)
    (timestamp dayIndex second : Nat)
    (timeBound : timestamp < 2 ^ 64)
    (dayBound : dayIndex < 2 ^ 48)
    (secondBound : second < 2 ^ 17)
    (equation : (timestamp : F) = (86400 : F) * (dayIndex : F) + (second : F)) :
    timestamp = 86400 * dayIndex + second := by
  have liftedBound : 86400 * dayIndex + second < 2 ^ 65 := by omega
  apply bounded_cast_injective (F := F) (p := p)
  · omega
  · omega
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using equation

set_option pp.all true in
#check @volume_context_cases
#print axioms volume_context_cases
set_option pp.all true in
#check @volume_external_requires_ordinary
#print axioms volume_external_requires_ordinary
set_option pp.all true in
#check @volume_timestamp_lift
#print axioms volume_timestamp_lift

/-- The native freshness upper bound keeps an Ordinary timestamp's day inside
the nullifier retention window. The day equation and second bound must come
from the same accepted timestamp; this says nothing about aggregate volume. -/
theorem volume_fresh_timestamp_within_retention (timestamp dayStart second now : Nat)
    (dayEquation : timestamp = dayStart + second)
    (secondBound : second < 86400)
    (freshUpper : now ≤ timestamp + 1800) : now < dayStart + 88200 := by
  omega

set_option pp.all true in
#check @volume_fresh_timestamp_within_retention
#print axioms volume_fresh_timestamp_within_retention
end ShielddSecurity
