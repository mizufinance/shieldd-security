import ShielddSecurity.Rows
import ShielddSecurity.Arithmetic

set_option maxHeartbeats 500000

namespace ShielddSecurity.Compiler

/-- Canonical sparse addition, independent of Commonware's BTreeMap code.
Zero removal and field reduction happen after integer coefficient collection. -/
def insertTerm (column : Nat) (coefficient : Int) : Linear → Linear
  | [] => [(column, coefficient)]
  | (other, value) :: tail =>
      if column = other then (other, coefficient + value) :: tail
      else if column < other then (column, coefficient) :: (other, value) :: tail
      else (other, value) :: insertTerm column coefficient tail

def collect : Linear → Linear
  | [] => []
  | (column, coefficient) :: tail => insertTerm column coefficient (collect tail)

def reduceCoefficients (p : Nat) : Linear → Linear
  | [] => []
  | (column, coefficient) :: tail =>
      let reduced := coefficient % (p : Int)
      if reduced = 0 then reduceCoefficients p tail
      else (column, reduced) :: reduceCoefficients p tail

def canonical (p : Nat) (terms : Linear) : Linear :=
  reduceCoefficients p (collect terms)

variable {F : Type} [Field F]

theorem eval_insert (rho : Nat → F) (column : Nat) (coefficient : Int) (terms : Linear) :
    eval rho (insertTerm column coefficient terms) = (coefficient : F) * rho column + eval rho terms := by
  induction terms with
  | nil => simp [insertTerm, eval]
  | cons head tail ih =>
      rcases head with ⟨other, value⟩
      by_cases equal : column = other
      · subst column
        simp [insertTerm, eval] <;> ring
      · by_cases before : column < other
        · simp [insertTerm, equal, before, eval]
        · simp [insertTerm, equal, before, eval, ih] <;> ring

theorem eval_collect (rho : Nat → F) (terms : Linear) :
    eval rho (collect terms) = eval rho terms := by
  induction terms with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨column, coefficient⟩
      simp only [collect, eval_insert, ih, eval]

theorem coefficient_mod {p : Nat} [CharP F p] (coefficient : Int) :
    ((coefficient % (p : Int) : Int) : F) = (coefficient : F) := by
  have divided := congrArg (fun n : Int => (n : F)) (Int.emod_add_ediv coefficient (p : Int))
  simpa [Int.cast_add, Int.cast_mul, CharP.cast_eq_zero F p] using divided

theorem eval_reduce {p : Nat} [CharP F p] (rho : Nat → F) (terms : Linear) :
    eval rho (reduceCoefficients p terms) = eval rho terms := by
  induction terms with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨column, coefficient⟩
      have reduced := coefficient_mod (F := F) (p := p) coefficient
      by_cases zero : coefficient % (p : Int) = 0
      · have castZero : (coefficient : F) = 0 := reduced.symm.trans (by simp [zero])
        simp [reduceCoefficients, zero, eval, castZero, ih]
      · simp [reduceCoefficients, zero, eval, reduced, ih]

theorem eval_canonical {p : Nat} [CharP F p] (rho : Nat → F) (terms : Linear) :
    eval rho (canonical p terms) = eval rho terms := by
  rw [canonical, eval_reduce, eval_collect]

theorem canonical_equal {p : Nat} [CharP F p] (rho : Nat → F) (left right : Linear)
    (certificate : canonical p left = canonical p right) :
    eval rho left = eval rho right := by
  rw [← eval_canonical rho left, certificate, eval_canonical]

/-- A checked row can differ syntactically only by coefficient collection and
reduction modulo the exact field characteristic. No hash/row identity is used
as a replacement for this semantic normalization. -/
def checkRow (p : Nat) (rows : List Row) (expected : Row) : Bool :=
  rows.any (fun actual => decide
    (canonical p actual.a = canonical p expected.a ∧
     canonical p actual.b = canonical p expected.b))

theorem checked_row_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (rows : List Row) (expected : Row) (satisfied : Satisfies rho rows)
    (checked : checkRow p rows expected = true) :
    Square (eval rho expected.a) (eval rho expected.b) := by
  obtain ⟨actual, member, accepted⟩ := List.any_eq_true.mp checked
  have equalities := of_decide_eq_true accepted
  have actualRow := satisfied actual member
  rw [canonical_equal rho actual.a expected.a equalities.1,
      canonical_equal rho actual.b expected.b equalities.2] at actualRow
  exact actualRow

def subtract (left right : Linear) : Linear := left ++ scaleLinear (-1) right

theorem eval_subtract (rho : Nat → F) (left right : Linear) :
    eval rho (subtract left right) = eval rho left - eval rho right := by
  simp [subtract, eval_append, eval_scale, sub_eq_add_neg]

/-- Local Add certificate for a fused source DAG node. The output is allowed
to be a linear combination; no one-column-per-node fiction is introduced. -/
theorem checked_add_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (left right output : Linear)
    (checked : canonical p output = canonical p (left ++ right)) :
    eval rho output = eval rho left + eval rho right := by
  rw [canonical_equal rho output (left ++ right) checked, eval_append]

/-- Materialized source square. Deferred squares are retained as expressions
and need no artificial witness column; assertions still require their rows. -/
theorem checked_square_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (rows : List Row) (input output : Linear) (satisfied : Satisfies rho rows)
    (checked : checkRow p rows ⟨input, output⟩ = true) :
    eval rho output = eval rho input * eval rho input := by
  exact (checked_row_sound rho rows ⟨input, output⟩ satisfied checked).symm

/-- Materialized general product, including the compiler's difference-square
auxiliary. An arbitrary satisfying assignment determines the multiplication;
the honest value-source evaluator is never consulted. -/
theorem checked_product_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (rows : List Row) (left right output auxiliary : Linear)
    (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows)
    (minus : checkRow p rows ⟨subtract left right, auxiliary⟩ = true)
    (plus : checkRow p rows ⟨left ++ right, auxiliary ++ scaleLinear 4 output⟩ = true) :
    eval rho output = eval rho left * eval rho right := by
  have minusRow := checked_row_sound rho rows ⟨subtract left right, auxiliary⟩ satisfied minus
  have plusRow := checked_row_sound rho rows ⟨left ++ right, auxiliary ++ scaleLinear 4 output⟩ satisfied plus
  rw [eval_subtract] at minusRow
  simp only [eval_append, eval_scale, Int.cast_ofNat] at plusRow
  exact (product_encoding _ _ _ _ four minusRow plusRow).symm

theorem checked_assertion_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (rows : List Row) (left right : Linear) (satisfied : Satisfies rho rows)
    (checked : checkRow p rows ⟨subtract left right, []⟩ = true) :
    eval rho left = eval rho right := by
  have row := checked_row_sound rho rows ⟨subtract left right, []⟩ satisfied checked
  have zero := square_zero _ (by simpa [eval] using row)
  exact sub_eq_zero.mp (by simpa [eval_subtract] using zero)

/-- Pari outlines fixed column zero into a fresh private copy in every emitted
arithmetic row. Recovering the source LC therefore requires the emitted link;
the observer's use of column zero alone is not a proof that the copy is one. -/
def unoutline (copy : Nat) (terms : Linear) : Linear :=
  terms.map (fun term => (if term.1 = copy then 0 else term.1, term.2))

def unoutlineRows (copy : Nat) (rows : List Row) : List Row :=
  rows.map (fun row => ⟨unoutline copy row.a, unoutline copy row.b⟩)

theorem eval_unoutline (rho : Nat → F) (copy : Nat) (terms : Linear)
    (linked : rho copy = rho 0) : eval rho (unoutline copy terms) = eval rho terms := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      rcases term with ⟨column, coefficient⟩
      change (coefficient : F) * rho (if column = copy then 0 else column) +
        eval rho (unoutline copy tail) = (coefficient : F) * rho column + eval rho tail
      rw [ih]
      by_cases isCopy : column = copy
      · subst column
        simp only [ite_true, linked]
      · simp only [if_neg isCopy]

theorem unoutline_rows_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (copy : Nat) (rows : List Row) (satisfied : Satisfies rho rows)
    (link : checkRow p rows ⟨[(0, 1), (copy, -1)], []⟩ = true) :
    Satisfies rho (unoutlineRows copy rows) := by
  have equality := checked_assertion_sound rho rows [(0, 1)] [(copy, 1)] satisfied
    (by simpa [subtract, scaleLinear] using link)
  have linked : rho copy = rho 0 := by simpa [eval] using equality.symm
  intro row member
  obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
  subst row
  simpa only [eval_unoutline rho copy _ linked] using satisfied original originalMember

/-- The source language has exactly the two operations present in Commonware's
CircuitNode. Finite earlier-node references rule out forward edges and cycles.
Constants/inputs are flattened source leaves, not extra arithmetic operations. -/
inductive SourceNode (earlier : Nat) where
  | constant (coefficient : Int)
  | input (index : Nat)
  | add (left right : Fin earlier)
  | mul (left right : Fin earlier)

inductive Expression where
  | linear (terms : Linear)
  | square (base : Linear)
  deriving DecidableEq

def expressionValue (rho : Nat → F) : Expression → F
  | .linear terms => eval rho terms
  | .square base => eval rho base * eval rho base

def sourceValue {n : Nat} (inputs : Nat → F) (earlier : Fin n → F) : SourceNode n → F
  | .constant coefficient => (coefficient : F)
  | .input index => inputs index
  | .add left right => earlier left + earlier right
  | .mul left right => earlier left * earlier right

/-- A typed certificate cannot certify a different source operation or silently
replace an unsupported expression with zero. All equality/row premises are
finite data checks, not the desired semantic conclusion. Deferred squares can
be results, but cannot be consumed as linear placeholders by later nodes.
Declared boundary inputs are explicit LCs: this permits round-by-round
composition while preserving the preceding round's fused expressions. Their
source identity/support and semantic role must be checked at each boundary. -/
inductive NodeCertificate (p : Nat) (rows : List Row) (inputTerms : Nat → Linear)
    {n : Nat} (earlier : Fin n → Expression) : SourceNode n → Expression → Prop where
  | constant (coefficient : Int) (output : Linear)
      (equal : canonical p output = canonical p [(0, coefficient)]) :
      NodeCertificate p rows inputTerms earlier (.constant coefficient) (.linear output)
  | input (index : Nat) (output : Linear)
      (equal : canonical p output = canonical p (inputTerms index)) :
      NodeCertificate p rows inputTerms earlier (.input index) (.linear output)
  | add (left right : Fin n) (x y output : Linear)
      (leftExpression : earlier left = .linear x) (rightExpression : earlier right = .linear y)
      (equal : canonical p output = canonical p (x ++ y)) :
      NodeCertificate p rows inputTerms earlier (.add left right) (.linear output)
  | foldedLeft (left right : Fin n) (x y output : Linear) (coefficient : Int)
      (leftExpression : earlier left = .linear x) (rightExpression : earlier right = .linear y)
      (constant : canonical p x = canonical p [(0, coefficient)])
      (equal : canonical p output = canonical p (scaleLinear coefficient y)) :
      NodeCertificate p rows inputTerms earlier (.mul left right) (.linear output)
  | foldedRight (left right : Fin n) (x y output : Linear) (coefficient : Int)
      (leftExpression : earlier left = .linear x) (rightExpression : earlier right = .linear y)
      (constant : canonical p y = canonical p [(0, coefficient)])
      (equal : canonical p output = canonical p (scaleLinear coefficient x)) :
      NodeCertificate p rows inputTerms earlier (.mul left right) (.linear output)
  | deferred (left right : Fin n) (x y base : Linear)
      (leftExpression : earlier left = .linear x) (rightExpression : earlier right = .linear y)
      (leftEqual : canonical p base = canonical p x)
      (rightEqual : canonical p base = canonical p y) :
      NodeCertificate p rows inputTerms earlier (.mul left right) (.square base)
  | square (left right : Fin n) (x y output : Linear)
      (leftExpression : earlier left = .linear x) (rightExpression : earlier right = .linear y)
      (equal : canonical p x = canonical p y)
      (row : checkRow p rows ⟨x, output⟩ = true) :
      NodeCertificate p rows inputTerms earlier (.mul left right) (.linear output)
  | product (left right : Fin n) (x y output auxiliary : Linear)
      (leftExpression : earlier left = .linear x) (rightExpression : earlier right = .linear y)
      (minus : checkRow p rows ⟨subtract x y, auxiliary⟩ = true)
      (plus : checkRow p rows ⟨x ++ y, auxiliary ++ scaleLinear 4 output⟩ = true) :
      NodeCertificate p rows inputTerms earlier (.mul left right) (.linear output)

theorem node_certificate_sound {p n : Nat} [CharP F p]
    (rows : List Row) (inputTerms : Nat → Linear) (earlier : Fin n → Expression)
    (node : SourceNode n) (output : Expression)
    (certificate : NodeCertificate p rows inputTerms earlier node output)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) :
    expressionValue rho output = sourceValue (fun i => eval rho (inputTerms i))
      (fun i => expressionValue rho (earlier i)) node := by
  cases certificate with
  | constant coefficient output equal =>
      simpa [expressionValue, sourceValue, eval, one] using
        canonical_equal rho output [(0, coefficient)] equal
  | input index output equal =>
      simpa [expressionValue, sourceValue, eval] using
        canonical_equal rho output (inputTerms index) equal
  | add left right x y output hx hy equal =>
      simpa [sourceValue, expressionValue, hx, hy] using
        checked_add_sound rho x y output equal
  | foldedLeft left right x y output coefficient hx hy constant equal =>
      have input : eval rho x = (coefficient : F) := by
        simpa [eval, one] using canonical_equal rho x [(0, coefficient)] constant
      have result := canonical_equal rho output (scaleLinear coefficient y) equal
      simp only [sourceValue, expressionValue, hx, hy]
      rw [result, eval_scale, input]
  | foldedRight left right x y output coefficient hx hy constant equal =>
      have input : eval rho y = (coefficient : F) := by
        simpa [eval, one] using canonical_equal rho y [(0, coefficient)] constant
      have result := canonical_equal rho output (scaleLinear coefficient x) equal
      simp only [sourceValue, expressionValue, hx, hy]
      rw [result, eval_scale, input]
      ring
  | deferred left right x y base hx hy ex ey =>
      simp only [sourceValue, expressionValue, hx, hy]
      rw [canonical_equal rho base x ex]
      exact congrArg (fun z : F => eval rho x * z)
        ((canonical_equal rho base x ex).symm.trans (canonical_equal rho base y ey))
  | square left right x y output hx hy equal row =>
      simp only [sourceValue, expressionValue, hx, hy]
      rw [checked_square_sound rho rows x output satisfied row]
      exact congrArg (fun z : F => eval rho x * z) (canonical_equal rho x y equal)
  | product left right x y output auxiliary hx hy minus plus =>
      simpa [sourceValue, expressionValue, hx, hy] using
        checked_product_sound rho rows x y output auxiliary four satisfied minus plus

inductive AssertionCertificate (p : Nat) (rows : List Row) : Expression → Expression → Prop where
  | linear (left right : Linear)
      (checked : checkRow p rows ⟨subtract left right, []⟩ = true) :
      AssertionCertificate p rows (.linear left) (.linear right)
  | squareLinear (left right : Linear)
      (checked : checkRow p rows ⟨left, right⟩ = true) :
      AssertionCertificate p rows (.square left) (.linear right)
  | linearSquare (left right : Linear)
      (checked : checkRow p rows ⟨right, left⟩ = true) :
      AssertionCertificate p rows (.linear left) (.square right)
  | squares (left right auxiliary : Linear)
      (first : checkRow p rows ⟨left, auxiliary⟩ = true)
      (second : checkRow p rows ⟨right, auxiliary⟩ = true) :
      AssertionCertificate p rows (.square left) (.square right)

theorem assertion_certificate_sound {p : Nat} [CharP F p]
    (rows : List Row) (left right : Expression)
    (certificate : AssertionCertificate p rows left right)
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    expressionValue rho left = expressionValue rho right := by
  cases certificate with
  | linear left right checked =>
      exact checked_assertion_sound rho rows left right satisfied checked
  | squareLinear left right checked =>
      exact checked_row_sound rho rows ⟨left, right⟩ satisfied checked
  | linearSquare left right checked =>
      exact (checked_row_sound rho rows ⟨right, left⟩ satisfied checked).symm
  | squares left right auxiliary first second =>
      exact (checked_row_sound rho rows ⟨left, auxiliary⟩ satisfied first).trans
        (checked_row_sound rho rows ⟨right, auxiliary⟩ satisfied second).symm

/-- A closed dependency cone has unique sequential node identities, only
earlier references, bounded input indices, and an explicit assertion list.
The source exporter/expected-gadget checker must bind this data to the actual
Circuit; this structure is not evidence of that extraction by itself. -/
structure SourceGraph (inputs nodes : Nat) where
  node : (index : Fin nodes) → SourceNode index.val
  inputBound : ∀ index input, node index = .input input → input < inputs
  assertions : List (Fin nodes × Fin nodes)
  outputs : List (Fin nodes)

def SourceGraph.prior {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    {α : Type} (values : Fin nodes → α) (index : Fin nodes) : Fin index.val → α :=
  fun previous => values ⟨previous.val, Nat.lt_trans previous.isLt index.isLt⟩

def GraphSatisfies {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) (values : Fin nodes → F) : Prop :=
  (∀ index, values index = sourceValue inputValues (graph.prior values index) (graph.node index)) ∧
  (∀ assertion ∈ graph.assertions, values assertion.1 = values assertion.2)

theorem sourceValue_congr {n : Nat} (inputValues : Nat → F)
    (left right : Fin n → F) (node : SourceNode n)
    (agree : ∀ index, left index = right index) :
    sourceValue inputValues left node = sourceValue inputValues right node := by
  cases node <;> simp only [sourceValue, agree]

/-- Acyclic node equations determine every output, not only an unconstrained
local relation. The reference values need only compute the independently chosen
source operations; no assertion or desired security property is assumed of them.
Binding the selected graph to the intended hash algorithm remains a separate
expected-graph check. -/
theorem graph_values_unique {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) (left right : Fin nodes → F)
    (leftComputes : ∀ index, left index =
      sourceValue inputValues (graph.prior left index) (graph.node index))
    (rightComputes : ∀ index, right index =
      sourceValue inputValues (graph.prior right index) (graph.node index)) :
    left = right := by
  have agree : ∀ k, ∀ bound : k < nodes,
      left ⟨k, bound⟩ = right ⟨k, bound⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro bound
        rw [leftComputes ⟨k, bound⟩, rightComputes ⟨k, bound⟩]
        apply sourceValue_congr
        intro previous
        exact ih previous.val previous.isLt (Nat.lt_trans previous.isLt bound)
  funext index
  exact agree index.val index.isLt

/-- The complete selected cone is checked node-by-node and assertion-by-assertion.
Omitting a source assertion is an extraction/expected-graph mismatch, never
permitted by silently dropping a failing certificate. Outputs refer to the
same certified source identities. This is soundness, not DAG witness completion. -/
theorem graph_certificate_sound {p inputs nodes : Nat} [CharP F p]
    (graph : SourceGraph inputs nodes) (rows : List Row)
    (inputTerms : Nat → Linear) (expressions : Fin nodes → Expression)
    (nodeCertificates : ∀ index, NodeCertificate p rows inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index))
    (assertionCertificates : ∀ assertion ∈ graph.assertions,
      AssertionCertificate p rows (expressions assertion.1) (expressions assertion.2))
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) :
    GraphSatisfies graph (fun input => eval rho (inputTerms input))
      (fun index => expressionValue rho (expressions index)) := by
  constructor
  · intro index
    exact node_certificate_sound rows inputTerms (graph.prior expressions index)
      (graph.node index) (expressions index) (nodeCertificates index) rho one four satisfied
  · intro assertion member
    exact assertion_certificate_sound rows _ _ (assertionCertificates assertion member) rho satisfied

theorem graph_certificate_outputs {p inputs nodes : Nat} [CharP F p]
    (graph : SourceGraph inputs nodes) (rows : List Row)
    (inputTerms : Nat → Linear) (expressions : Fin nodes → Expression)
    (nodeCertificates : ∀ index, NodeCertificate p rows inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index))
    (assertionCertificates : ∀ assertion ∈ graph.assertions,
      AssertionCertificate p rows (expressions assertion.1) (expressions assertion.2))
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) (reference : Fin nodes → F)
    (computes : ∀ index, reference index = sourceValue
      (fun input => eval rho (inputTerms input)) (graph.prior reference index) (graph.node index)) :
    graph.outputs.map (fun index => expressionValue rho (expressions index)) =
      graph.outputs.map reference := by
  have semantics := graph_certificate_sound graph rows inputTerms expressions
    nodeCertificates assertionCertificates rho one four satisfied
  have unique := graph_values_unique graph (fun input => eval rho (inputTerms input))
    (fun index => expressionValue rho (expressions index)) reference semantics.1 computes
  rw [unique]

#print axioms canonical_equal
#print axioms checked_add_sound
#print axioms checked_square_sound
#print axioms checked_product_sound
#print axioms checked_assertion_sound
#print axioms unoutline_rows_sound
#print axioms node_certificate_sound
#print axioms assertion_certificate_sound
#print axioms graph_certificate_sound
#print axioms graph_values_unique
#print axioms graph_certificate_outputs

end ShielddSecurity.Compiler
