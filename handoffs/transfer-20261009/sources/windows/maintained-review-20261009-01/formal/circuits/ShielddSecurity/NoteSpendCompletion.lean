import ShielddSecurity.ScalarCompletion
import ShielddSecurity.PermanentSpend

set_option maxHeartbeats 500000

namespace ShielddSecurity.NoteSpendCompletion

variable {F : Type} [Field F]

/-- Current note.rs optional-spend semantics, after independently constructing
the NOTE / NOTE_NULLIFIER / DUMMY_NULLIFIER hashes and the state-tree root.
The synthetic hash uses the Transfer padding family, shared randomizer, and
fixed slot 1. Hash/Merkle construction and range blocks are separate joins. -/
structure Values (F : Type) where
  dummy : Bool
  synthetic : F
  realNullifier : F
  nullifier : F
  computedAnchor : F
  anchor : F
  amount : F

def Values.Legal (v : Values F) : Prop :=
  v.nullifier = (if v.dummy then v.synthetic else v.realNullifier) ∧
  (v.dummy = false → v.computedAnchor = v.anchor) ∧
  (v.dummy = true → v.amount = 0)

def Values.bit (v : Values F) : F := if v.dummy then 1 else 0

theorem values_branch (v : Values F) (legal : v.Legal) :
    PermanentSpend.BranchSpec v.bit v.amount v.nullifier v.realNullifier
      v.synthetic v.computedAnchor v.anchor := by
  rcases v with ⟨dummy, synthetic, realNullifier, nullifier, computedAnchor, anchor, amount⟩
  cases dummy
  · exact Or.inl ⟨rfl, legal.1, legal.2.1 rfl⟩
  · exact Or.inr ⟨rfl, legal.2.2 rfl, legal.1⟩

theorem branch_equations (v : Values F) (legal : v.Legal) :
    v.bit * (v.synthetic - v.realNullifier) = v.nullifier - v.realNullifier ∧
    (1 - v.bit) * (v.computedAnchor - v.anchor) = 0 ∧
    v.bit * v.amount = 0 := by
  have gates := PermanentSpend.branch_gates_complete v.bit v.amount v.nullifier
    v.realNullifier v.synthetic v.computedAnchor v.anchor (values_branch v legal)
  refine ⟨?_, gates.2.2⟩
  calc
    _ = v.bit * v.synthetic + (1 - v.bit) * v.realNullifier - v.realNullifier := by ring
    _ = _ := by rw [← gates.2.1]

theorem branch_boolean (v : Values F) : Square v.bit v.bit := by
  cases h : v.dummy <;> simp [Square, Values.bit, h]

/-- One materialized multiplication and its assertion, with only the actual
fresh product pivot and minus-square auxiliary owned by the extension. -/
structure Gate where
  left : Linear
  right : Linear
  target : Linear
  product : Nat
  auxiliary : Nat

def Gate.writes (g : Gate) : List Nat := [g.product, g.auxiliary]
def Gate.inputs (g : Gate) : Linear := g.left ++ g.right ++ g.target
def Gate.rows (g : Gate) : List Row :=
  ScalarCompletion.productRows g.left g.right [] g.product g.auxiliary ++
    [⟨Compiler.subtract [(g.product, 1)] g.target, []⟩]
def Gate.extend (g : Gate) (base : Nat → F) : Nat → F :=
  ScalarCompletion.extendProduct base g.left g.right [] g.product g.auxiliary
def Gate.Equation (g : Gate) (base : Nat → F) : Prop :=
  eval base g.left * eval base g.right = eval base g.target

theorem gate_preserves (g : Gate) (base : Nat → F) (column : Nat)
    (outside : column ∉ g.writes) : g.extend base column = base column :=
  ScalarCompletion.extend_product_preserves base g.left g.right []
    g.product g.auxiliary column outside

theorem gate_eval_preserves (g : Gate) (base : Nat → F) (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 ∉ g.writes) :
    eval (g.extend base) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact gate_preserves g base term.1 (outside term member)

theorem gate_equation_preserves (g h : Gate) (base : Nat → F)
    (outside : ∀ term ∈ h.inputs, term.1 ∉ g.writes)
    (equation : h.Equation base) : h.Equation (g.extend base) := by
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ h.inputs) :
      eval (g.extend base) terms = eval base terms := by
    apply gate_eval_preserves
    intro term member
    exact outside term (included term member)
  change eval (g.extend base) h.left * eval (g.extend base) h.right =
    eval (g.extend base) h.target
  rw [agrees h.left (by intro term member; simp [Gate.inputs, member]),
    agrees h.right (by intro term member; simp [Gate.inputs, member]),
    agrees h.target (by intro term member; simp [Gate.inputs, member])]
  exact equation

theorem gate_complete (g : Gate) (base : Nat → F)
    (distinct : g.product ≠ g.auxiliary)
    (fresh : ∀ term ∈ g.inputs, term.1 ∉ g.writes)
    (equation : g.Equation base) : Satisfies (g.extend base) g.rows := by
  have productRows := ScalarCompletion.extend_product_complete base g.left g.right []
    g.product g.auxiliary distinct (by
      intro term member
      have present : term ∈ g.left ++ g.right := by simpa using member
      rcases List.mem_append.mp present with present | present
      · exact fresh term (by simp [Gate.inputs, present])
      · exact fresh term (by simp [Gate.inputs, present]))
  have targetValue : eval (g.extend base) g.target = eval base g.target := by
    apply gate_eval_preserves
    intro term member
    exact fresh term (by simp [Gate.inputs, member])
  have productValue : g.extend base g.product = eval base g.left * eval base g.right := by
    simp [Gate.extend, ScalarCompletion.extendProduct, ScalarCompletion.productValues,
      patchAssignment, eval]
  intro row member
  rcases List.mem_append.mp member with materialization | assertion
  · exact productRows row materialization
  · simp only [List.mem_singleton] at assertion
    subst row
    simp only [Square, Compiler.eval_subtract, eval, Int.cast_one, one_mul,
      add_zero, productValue, targetValue]
    rw [show eval base g.left * eval base g.right = eval base g.target from equation]
    simp

theorem gate_preserves_rows (g : Gate) (base : Nat → F) (rows : List Row)
    (satisfied : Satisfies base rows)
    (outside : ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ g.writes) :
    Satisfies (g.extend base) rows :=
  ScalarCompletion.extend_product_preserves_rows base g.left g.right []
    g.product g.auxiliary rows satisfied outside

structure Inputs where
  dummy : Linear
  synthetic : Linear
  realNullifier : Linear
  nullifier : Linear
  computedAnchor : Linear
  anchor : Linear
  amount : Linear

def Inputs.Represents (i : Inputs) (base : Nat → F) (v : Values F) : Prop :=
  eval base i.dummy = v.bit ∧ eval base i.synthetic = v.synthetic ∧
  eval base i.realNullifier = v.realNullifier ∧ eval base i.nullifier = v.nullifier ∧
  eval base i.computedAnchor = v.computedAnchor ∧ eval base i.anchor = v.anchor ∧
  eval base i.amount = v.amount

/-- The three current source products: BoolVar.select is false + bit*(true-false),
then (1-dummy)*(computedAnchor-anchor), then dummy*amount. -/
def selector (i : Inputs) (product auxiliary : Nat) : Gate :=
  ⟨i.dummy, Compiler.subtract i.synthetic i.realNullifier,
    Compiler.subtract i.nullifier i.realNullifier, product, auxiliary⟩
def anchorGate (i : Inputs) (product auxiliary : Nat) : Gate :=
  ⟨Compiler.subtract [(0, 1)] i.dummy,
    Compiler.subtract i.computedAnchor i.anchor, [], product, auxiliary⟩
def amountGate (i : Inputs) (product auxiliary : Nat) : Gate :=
  ⟨i.dummy, i.amount, [], product, auxiliary⟩

theorem source_equations (i : Inputs) (base : Nat → F) (v : Values F)
    (one : base 0 = 1) (represented : i.Represents base v) (legal : v.Legal)
    (sp sa rp ra ap aa : Nat) :
    (selector i sp sa).Equation base ∧ (anchorGate i rp ra).Equation base ∧
    (amountGate i ap aa).Equation base := by
  rcases represented with ⟨dummy, synthetic, realNF, publishedNF, computed, anchor, amount⟩
  simpa only [Gate.Equation, selector, anchorGate, amountGate, Compiler.eval_subtract,
    eval, Int.cast_one, one_mul, add_zero, one, dummy, synthetic, realNF,
    publishedNF, computed, anchor, amount] using branch_equations v legal

def complete (base : Nat → F) (s r a : Gate) : Nat → F :=
  a.extend (r.extend (s.extend base))

theorem complete_preserves (base : Nat → F) (s r a : Gate) (column : Nat)
    (outside : column ∉ s.writes ++ r.writes ++ a.writes) :
    complete base s r a column = base column := by
  have hs : column ∉ s.writes := by intro present; exact outside (by simp [present])
  have hr : column ∉ r.writes := by intro present; exact outside (by simp [present])
  have ha : column ∉ a.writes := by intro present; exact outside (by simp [present])
  exact (gate_preserves a _ column ha).trans
    ((gate_preserves r _ column hr).trans (gate_preserves s base column hs))

theorem complete_preserves_rows (base : Nat → F) (s r a : Gate) (prior : List Row)
    (satisfied : Satisfies base prior)
    (outside : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
      term.1 ∉ s.writes ++ r.writes ++ a.writes) :
    Satisfies (complete base s r a) prior := by
  intro row member
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (complete base s r a) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact complete_preserves base s r a term.1 (outside row member term (included term present))
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact satisfied row member

/-- Complete only these current optional-spend branch rows. All semantic branch
equations are derived above. The syntactic ownership hypotheses require exact
source supports and later-write exclusion, not already-satisfied branch rows.
No assertion that other Transfer rows survive these six writes is made. -/
theorem optional_spend_complete (i : Inputs) (base : Nat → F) (v : Values F)
    (one : base 0 = 1) (represented : i.Represents base v) (legal : v.Legal)
    (sp sa rp ra ap aa : Nat)
    (distinct : sp ≠ sa ∧ rp ≠ ra ∧ ap ≠ aa)
    (fresh : ∀ g ∈ [selector i sp sa, anchorGate i rp ra, amountGate i ap aa],
      ∀ term ∈ g.inputs, term.1 ∉
        (selector i sp sa).writes ++ (anchorGate i rp ra).writes ++ (amountGate i ap aa).writes)
    (anchorSafe : ∀ row ∈ (selector i sp sa).rows,
      ∀ term ∈ row.a ++ row.b, term.1 ∉ (anchorGate i rp ra).writes)
    (amountSafe : ∀ row ∈ (selector i sp sa).rows ++ (anchorGate i rp ra).rows,
      ∀ term ∈ row.a ++ row.b, term.1 ∉ (amountGate i ap aa).writes) :
    Satisfies (complete base (selector i sp sa) (anchorGate i rp ra) (amountGate i ap aa))
      ([⟨i.dummy, i.dummy⟩] ++ (selector i sp sa).rows ++
        (anchorGate i rp ra).rows ++ (amountGate i ap aa).rows) ∧
    (∀ column, column ∉ [sp, sa] ++ [rp, ra] ++ [ap, aa] →
      complete base (selector i sp sa) (anchorGate i rp ra) (amountGate i ap aa) column = base column) := by
  let s := selector i sp sa
  let r := anchorGate i rp ra
  let a := amountGate i ap aa
  have owns (g : Gate) (member : g ∈ [s, r, a]) (h : Gate) (hmember : h ∈ [s, r, a]) :
      ∀ term ∈ g.inputs, term.1 ∉ h.writes := by
    intro term present outside
    have full := fresh g member term present
    change term.1 ∉ s.writes ++ r.writes ++ a.writes at full
    apply full
    rcases (by simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hmember :
      h = s ∨ h = r ∨ h = a) with rfl | rfl | rfl <;> simp [outside]
  have equations := source_equations i base v one represented legal sp sa rp ra ap aa
  have first := gate_complete s base distinct.1 (owns s (by simp) s (by simp)) equations.1
  have secondEq := gate_equation_preserves s r base (owns r (by simp) s (by simp)) equations.2.1
  have second := gate_complete r (s.extend base) distinct.2.1
    (owns r (by simp) r (by simp)) secondEq
  have firstKept := gate_preserves_rows r (s.extend base) s.rows first anchorSafe
  have firstTwo : Satisfies (r.extend (s.extend base)) (s.rows ++ r.rows) := by
    intro row present
    rcases List.mem_append.mp present with present | present
    · exact firstKept row present
    · exact second row present
  have thirdEq := gate_equation_preserves r a (s.extend base) (owns a (by simp) r (by simp))
    (gate_equation_preserves s a base (owns a (by simp) s (by simp)) equations.2.2)
  have third := gate_complete a (r.extend (s.extend base)) distinct.2.2
    (owns a (by simp) a (by simp)) thirdEq
  have earlier := gate_preserves_rows a (r.extend (s.extend base)) (s.rows ++ r.rows) firstTwo amountSafe
  have dummyPreserved (g : Gate) (member : g ∈ [s, r, a]) (rho : Nat → F) :
      eval (g.extend rho) i.dummy = eval rho i.dummy := by
    apply gate_eval_preserves
    intro term present
    exact owns s (by simp) g member term (by simp [s, selector, Gate.inputs, present])
  have dummyValue : eval (complete base s r a) i.dummy = v.bit := by
    change eval (a.extend (r.extend (s.extend base))) i.dummy = v.bit
    rw [dummyPreserved a (by simp), dummyPreserved r (by simp), dummyPreserved s (by simp)]
    exact represented.1
  constructor
  · intro row present
    change row ∈ [⟨i.dummy, i.dummy⟩] ++ s.rows ++ r.rows ++ a.rows at present
    have grouped : row ∈ [⟨i.dummy, i.dummy⟩] ++ ((s.rows ++ r.rows) ++ a.rows) := by
      simpa only [List.append_assoc] using present
    rcases List.mem_append.mp grouped with present | present
    · simp only [List.mem_singleton] at present
      subst row
      change Square (eval (complete base s r a) i.dummy) (eval (complete base s r a) i.dummy)
      rw [dummyValue]
      exact branch_boolean v
    · rcases List.mem_append.mp present with present | present
      · exact earlier row present
      · exact third row present
  · intro column outside
    exact complete_preserves base s r a column outside

set_option pp.all true in
#check @values_branch
#print axioms values_branch
set_option pp.all true in
#check @branch_equations
#print axioms branch_equations
set_option pp.all true in
#check @branch_boolean
#print axioms branch_boolean
set_option pp.all true in
#check @gate_preserves
#print axioms gate_preserves
set_option pp.all true in
#check @gate_eval_preserves
#print axioms gate_eval_preserves
set_option pp.all true in
#check @gate_equation_preserves
#print axioms gate_equation_preserves
set_option pp.all true in
#check @gate_complete
#print axioms gate_complete
set_option pp.all true in
#check @gate_preserves_rows
#print axioms gate_preserves_rows
set_option pp.all true in
#check @source_equations
#print axioms source_equations
set_option pp.all true in
#check @complete_preserves
#print axioms complete_preserves
set_option pp.all true in
#check @complete_preserves_rows
#print axioms complete_preserves_rows
set_option pp.all true in
#check @optional_spend_complete
#print axioms optional_spend_complete

end ShielddSecurity.NoteSpendCompletion
