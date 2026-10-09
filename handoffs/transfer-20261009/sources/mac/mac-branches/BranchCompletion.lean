import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 400000

/- Original constructive integer/Boolean branch model. Runtime pin:
844389ee069e1fb2e576708842d0b389b4d9a44a. No Shieldd proofs imported.
Actual full native-circuit witness replay is separate in native_branch_harness.rs.
This model closes selector/inactive-arithmetic completion under explicit lifted
range/tree/hash prerequisites; it does not assert compiler-row refinement. -/
namespace MacBranches
def B : Int := 340282366920938463463374607431768211456
def bit (b : Bool) : Int := if b then 1 else 0
inductive Mode where
  | padding | origin | continuation
  deriving DecidableEq
def real (m : Mode) : Bool := m != .padding

structure Branch where
  fee : Bool
  regulated : Bool
  external : Bool
  dummySecond : Bool
  mode : Mode
  deriving DecidableEq

def eligible (b : Branch) : Bool := !b.fee && b.regulated && b.external
def flagged (b : Branch) : Bool := eligible b && !real b.mode
def legal (b : Branch) : Prop :=
  (b.fee = true → b.external = false) ∧
  (real b.mode = true → eligible b = true)

def context (b : Branch) : Int := 1 + bit b.fee

theorem fee_has_no_real_or_flag (b : Branch) (h : legal b) (fee : b.fee = true) :
    real b.mode = false ∧ flagged b = false ∧ b.external = false := by
  have ext := h.1 fee
  have r : real b.mode = false := by
    cases eq : real b.mode
    · rfl
    · have e := h.2 eq
      simp [eligible, fee] at e
  exact ⟨r, by simp [flagged, eligible, fee], ext⟩

theorem full_context_gate_complete (b : Branch) (h : legal b) :
    (context b - 1) * bit b.external = 0 := by
  cases fee : b.fee
  · simp [context, bit, fee]
  · have e := h.1 fee
    simp [context, bit, fee, e]

theorem real_gate_complete (b : Branch) (h : legal b) :
    bit (real b.mode) * (1 - bit (eligible b)) = 0 := by
  cases r : real b.mode
  · simp [bit, r]
  · have e := h.2 r
    simp [bit, r, e]

theorem optional_dummy_amount_completion (dummy : Bool) (second : Int)
    (h : dummy = true → second = 0) : bit dummy * second = 0 := by
  cases d : dummy
  · simp [bit, d]
  · simp [bit, d, h d]

-- Mandatory real spend's path is never suppressed; optional real spend uses
-- its supplied legal path. A dummy can use any bounded path with amount zero.
def optionalRows (dummy : Bool) (amount root anchor nf realNF dummyNF : Int) : Prop :=
  (1-bit dummy)*(root-anchor) = 0 ∧ bit dummy*amount = 0 ∧
  nf = if dummy then dummyNF else realNF

theorem optional_path_completion (dummy : Bool) (amount root anchor realNF dummyNF : Int)
    (zero : dummy = true → amount = 0)
    (membership : dummy = false → root = anchor) :
    ∃ nf, optionalRows dummy amount root anchor nf realNF dummyNF := by
  refine ⟨if dummy then dummyNF else realNF, ?_⟩
  cases d : dummy
  · simp [optionalRows, bit, d, membership d]
  · simp [optionalRows, bit, d, zero d]

-- Exact lifted arithmetic of volume.rs:104–116, including the unconditional
-- candidate bound in inactive branches. Padding construction chooses prior=0.
structure NumericInput where
  receiver : Int
  realPrior : Int
  limit : Int

def prior (b : Branch) (n : NumericInput) : Int := if real b.mode then n.realPrior else 0
def candidate (b : Branch) (n : NumericInput) : Int := prior b n + n.receiver
def successor (b : Branch) (n : NumericInput) : Int := if real b.mode then candidate b n else 0
def numericLegal (b : Branch) (n : NumericInput) : Prop :=
  0 < n.receiver ∧ n.receiver < B ∧ 0 ≤ n.realPrior ∧ n.realPrior < B ∧
  0 ≤ n.limit ∧ n.limit < B ∧
  (real b.mode = true → n.realPrior + n.receiver < B ∧ n.realPrior + n.receiver ≤ n.limit) ∧
  (b.mode = .origin → n.realPrior = 0)

theorem candidate_always_bounded (b : Branch) (n : NumericInput) (h : numericLegal b n) :
    0 ≤ candidate b n ∧ candidate b n < B := by
  have positive := h.1
  have nonnegative := h.2.2.1
  cases r : real b.mode
  · simp [candidate, prior, r]
    exact ⟨by omega, h.2.1⟩
  · have a := (h.2.2.2.2.2.2.1 r).1
    simp [candidate, prior, r]
    omega

-- Construct a comparison witness for candidate ≤ limit or candidate > limit.
-- Both operands are bounded even when the limit comparison is inactive.
theorem bounded_comparator_constructive (x y : Int)
    (hx : 0 ≤ x ∧ x < B) (hy : 0 ≤ y ∧ y < B) :
    ∃ difference borrow : Int, 0 ≤ difference ∧ difference < B ∧
      (borrow = 0 ∨ borrow = 1) ∧ y-x = difference-borrow*B ∧
      (borrow = 0 ↔ x ≤ y) := by
  by_cases le : x ≤ y
  · refine ⟨y-x, 0, ?_⟩
    simp [B] at *
    omega
  · refine ⟨B+y-x, 1, ?_⟩
    simp [B] at *
    omega

def numericalRows (b : Branch) (n : NumericInput) (difference borrow : Int) : Prop :=
  0 ≤ prior b n ∧ prior b n < B ∧
  0 ≤ successor b n ∧ successor b n < B ∧
  0 ≤ candidate b n ∧ candidate b n < B ∧
  0 ≤ difference ∧ difference < B ∧ (borrow = 0 ∨ borrow = 1) ∧
  n.limit-candidate b n = difference-borrow*B ∧
  bit (real b.mode)*(successor b n-candidate b n) = 0 ∧
  bit (real b.mode)*borrow = 0 ∧
  (b.mode = .origin → prior b n = 0)

theorem volume_arithmetic_auxiliaries_complete (b : Branch) (n : NumericInput)
    (h : numericLegal b n) : ∃ difference borrow, numericalRows b n difference borrow := by
  have bounded := candidate_always_bounded b n h
  obtain ⟨d, q, hd0, hdB, hq, heq, iff⟩ := bounded_comparator_constructive
    (candidate b n) n.limit bounded ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  refine ⟨d, q, ?_⟩
  have p : 0 ≤ prior b n ∧ prior b n < B := by
    cases r : real b.mode
    · simp [prior, r, B]
    · simpa [prior, r] using And.intro h.2.2.1 h.2.2.2.1
  have s : 0 ≤ successor b n ∧ successor b n < B := by
    cases r : real b.mode
    · simp [successor, r, B]
    · simpa [successor, r] using bounded
  have update : bit (real b.mode)*(successor b n-candidate b n) = 0 := by
    cases r : real b.mode <;> simp [bit, successor, r]
  have gate : bit (real b.mode)*q = 0 := by
    cases r : real b.mode
    · simp [bit, r]
    · have le : candidate b n ≤ n.limit := by
        simpa [candidate, prior, r] using (h.2.2.2.2.2.2.1 r).2
      have q0 := iff.mpr le
      simp [bit, r, q0]
  have origin : b.mode = .origin → prior b n = 0 := by
    intro m
    have zero := h.2.2.2.2.2.2.2 m
    simp [prior, m, real, zero]
  exact ⟨p.1, p.2, s.1, s.2, bounded.1, bounded.2, hd0, hdB,
    hq, heq, update, gate, origin⟩

-- Inactive branches need not satisfy receiver ≤ limit. Their normalized prior
-- and comparator witnesses still satisfy ALL unconditional arithmetic rows.
theorem padding_over_limit_has_constructive_auxiliaries :
    ∃ d q, numericalRows ⟨false,true,true,true,.padding⟩ ⟨25,0,1⟩ d q := by
  apply volume_arithmetic_auxiliaries_complete
  simp [numericLegal, real, B]

-- A padding witness with arbitrary unbounded prior is NOT automatically legal.
theorem inactive_candidate_overflow_control :
    ∃ priorValue receiver : Int, 0 ≤ priorValue ∧ priorValue < B ∧
      0 < receiver ∧ receiver < B ∧ ¬ priorValue+receiver < B := by
  exact ⟨B-1, 1, by simp [B]⟩

#print axioms fee_has_no_real_or_flag
#print axioms full_context_gate_complete
#print axioms real_gate_complete
#print axioms optional_dummy_amount_completion
#print axioms optional_path_completion
#print axioms candidate_always_bounded
#print axioms bounded_comparator_constructive
#print axioms volume_arithmetic_auxiliaries_complete
#print axioms padding_over_limit_has_constructive_auxiliaries
#print axioms inactive_candidate_overflow_control
end MacBranches
