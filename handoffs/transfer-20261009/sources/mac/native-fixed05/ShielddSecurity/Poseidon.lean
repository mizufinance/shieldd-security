import ShielddSecurity.Compiler

set_option maxHeartbeats 500000

namespace ShielddSecurity.Poseidon

variable {F : Type} [Field F]

/-- Independent mathematical round specification. Parameters are explicit data:
the qualified instance must check the exact 65 round constants and MDS entries
from both deployed artifacts, not merely assume an arbitrary secure permutation.
Collision resistance is not a conclusion of this arithmetic specification. -/
abbrev State (F : Type) (width : Nat) := Fin width → F

structure Parameters (F : Type) (width : Nat) where
  ark : Nat → State F width
  mds : Fin width → State F width

def nonlinear (round index : Nat) : Bool :=
  decide (round < 4 ∨ 61 ≤ round ∨ index = 0)

def mix {width : Nat} (matrix : Fin width → State F width) (state : State F width) :
    State F width := fun row =>
  (List.finRange width).foldl (fun total column => total + matrix row column * state column) 0

def round {width : Nat} (parameters : Parameters F width) (index : Nat)
    (state : State F width) : State F width :=
  mix parameters.mds (fun column =>
    let value := state column + parameters.ark index column
    if nonlinear index column.val then value ^ 5 else value)

def rounds {width : Nat} (parameters : Parameters F width) :
    Nat → State F width → State F width
  | 0, state => state
  | count + 1, state => round parameters count (rounds parameters count state)

def permute {width : Nat} (parameters : Parameters F width) (state : State F width) :=
  rounds parameters 65 state

def chunks2 : List F → List (List F)
  | [] => []
  | [first] => [[first]]
  | first :: second :: rest => [first, second] :: chunks2 rest

def chunks5 : List F → List (List F)
  | [] => []
  | [a] => [[a]]
  | [a, b] => [[a, b]]
  | [a, b, c] => [[a, b, c]]
  | [a, b, c, d] => [[a, b, c, d]]
  | a :: b :: c :: d :: e :: rest => [a, b, c, d, e] :: chunks5 rest

def initial {width : Nat} (domain arity : Nat) : State F width :=
  fun column => if column.val = 0 then ((arity * 256 + domain : Nat) : F) else 0

def absorb {width : Nat} (state : State F width) (chunk : List F) : State F width :=
  fun column => if column.val = 0 then state column
    else state column + chunk[column.val - 1]?.getD 0

/-- Absorption is additive into rate positions, with no overwrite or extra
padding marker; the domain/arity IV supplies framing. Empty input still performs
one permutation. Only hash3/hash6 below supply the deployed fixed chunk widths. -/
def sponge {width : Nat} (parameters : Parameters F width) (domain arity : Nat)
    (chunks : List (List F)) : State F width :=
  match chunks with
  | [] => permute parameters (initial domain arity)
  | _ :: _ => chunks.foldl
      (fun state chunk => permute parameters (absorb state chunk)) (initial domain arity)

def hash3 (parameters : Parameters F 3) (domain : Nat) (inputs : List F) : F :=
  sponge parameters domain inputs.length (chunks2 inputs) ⟨1, by decide⟩

def hash6 (parameters : Parameters F 6) (domain : Nat) (inputs : List F) : F :=
  sponge parameters domain inputs.length (chunks5 inputs) ⟨1, by decide⟩

/-- One checked absorption/permutation block gives the full wide hash only when
the actual ordered inputs form exactly one chunk and its initial state agrees.
The block equation is supplied by row certificates, not an honest evaluator. -/
theorem hash6_of_one_block (parameters : Parameters F 6) (domain : Nat)
    (inputs : List F) (before after : State F 6)
    (chunks : chunks5 inputs = [inputs])
    (initialState : before = initial domain inputs.length)
    (block : after = permute parameters (absorb before inputs)) :
    after ⟨1, by decide⟩ = hash6 parameters domain inputs := by
  rw [hash6, chunks, sponge]
  simpa only [List.foldl_cons, List.foldl_nil, ← initialState] using
    congrArg (fun state : State F 6 => state ⟨1, by decide⟩) block

def hash (small : Parameters F 3) (wide : Parameters F 6)
    (domain : Nat) (inputs : List F) : F :=
  if inputs.length ≤ 2 then hash3 small domain inputs else hash6 wide domain inputs

theorem domain_arity_injective (domain otherDomain arity otherArity : Nat)
    (domainBound : domain < 256) (otherBound : otherDomain < 256)
    (equal : arity * 256 + domain = otherArity * 256 + otherDomain) :
    domain = otherDomain ∧ arity = otherArity := by
  omega

/-- The expected arithmetic construction uses only constants/Add/Mul. A later
closed source-DAG check must establish that actual source operations have this
shape. This interpreter does not make the Rust construction faithful by decree. -/
structure Operations (F A : Type) where
  constant : F → A
  add : A → A → A
  mul : A → A → A

def fifth {A : Type} (ops : Operations F A) (value : A) : A :=
  let square := ops.mul value value
  ops.mul (ops.mul square square) value

def roundOps {width : Nat} {A : Type} (ops : Operations F A)
    (parameters : Parameters F width) (index : Nat) (state : State A width) : State A width :=
  let transformed := fun column : Fin width =>
    let value := ops.add (state column) (ops.constant (parameters.ark index column))
    if nonlinear index column.val then fifth ops value else value
  fun row => (List.finRange width).foldl
    (fun total column => ops.add total
      (ops.mul (ops.constant (parameters.mds row column)) (transformed column)))
    (ops.constant 0)

def roundsOps {width : Nat} {A : Type} (ops : Operations F A)
    (parameters : Parameters F width) : Nat → State A width → State A width
  | 0, state => state
  | count + 1, state => roundOps ops parameters count (roundsOps ops parameters count state)

/-- Laws of an arithmetic interpretation, not assumptions about arbitrary finite
compiled node IDs. The free syntax below discharges all three definitionally;
actual source nodes are joined separately through finite DAG certificates. -/
structure Evaluates {A : Type} (ops : Operations F A) (value : A → F) : Prop where
  constant : ∀ coefficient, value (ops.constant coefficient) = coefficient
  add : ∀ left right, value (ops.add left right) = value left + value right
  mul : ∀ left right, value (ops.mul left right) = value left * value right

inductive Arithmetic (F : Type) where
  | constant (coefficient : F)
  | input (index : Nat)
  | add (left right : Arithmetic F)
  | mul (left right : Arithmetic F)

def arithmeticValue (inputs : Nat → F) : Arithmetic F → F
  | .constant coefficient => coefficient
  | .input index => inputs index
  | .add left right => arithmeticValue inputs left + arithmeticValue inputs right
  | .mul left right => arithmeticValue inputs left * arithmeticValue inputs right

def arithmeticOperations : Operations F (Arithmetic F) :=
  ⟨Arithmetic.constant, Arithmetic.add, Arithmetic.mul⟩

theorem arithmetic_evaluates (inputs : Nat → F) :
    Evaluates arithmeticOperations (arithmeticValue inputs) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem fifth_evaluates {A : Type} (ops : Operations F A) (value : A → F)
    (laws : Evaluates ops value) (input : A) :
    value (fifth ops input) = value input ^ 5 := by
  simp only [fifth, laws.mul]
  ring

theorem fold_evaluates {A I : Type} (ops : Operations F A) (value : A → F)
    (laws : Evaluates ops value) (items : List I) (term : I → A) (initial : A) :
    value (items.foldl (fun total item => ops.add total (term item)) initial) =
      items.foldl (fun total item => total + value (term item)) (value initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.foldl_cons, laws.add] using ih (ops.add initial (term head))

theorem round_evaluates {width : Nat} {A : Type} (ops : Operations F A)
    (value : A → F) (laws : Evaluates ops value) (parameters : Parameters F width)
    (index : Nat) (state : State A width) :
    (fun column => value (roundOps ops parameters index state column)) =
      round parameters index (fun column => value (state column)) := by
  funext row
  unfold roundOps round mix
  rw [fold_evaluates ops value laws]
  simp only [laws.constant, laws.mul, laws.add]
  congr 1
  funext total column
  split <;> simp_all only [fifth_evaluates ops value laws, laws.add, laws.constant]

theorem rounds_evaluate {width : Nat} {A : Type} (ops : Operations F A)
    (value : A → F) (laws : Evaluates ops value) (parameters : Parameters F width)
    (count : Nat) (state : State A width) :
    (fun column => value (roundsOps ops parameters count state column)) =
      rounds parameters count (fun column => value (state column)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (fun column => value (roundOps ops parameters count
        (roundsOps ops parameters count state) column)) =
        round parameters count (rounds parameters count (fun column => value (state column)))
      rw [round_evaluates ops value laws, ih]

/-- No honest-witness/operator assumption: the expected arithmetic expression
computes the mathematical permutation for every field assignment. Runtime
certificates must still prove their finite DAG is this expected construction.
Generation keeps sharing and proves round composition; it must not expand the
entire 65-round tree into an exponentially large proof term. -/
theorem expected_permutation_evaluates {width : Nat} (parameters : Parameters F width)
    (inputs : Nat → F) (state : State (Arithmetic F) width) :
    (fun column => arithmeticValue inputs
      (roundsOps arithmeticOperations parameters 65 state column)) =
      permute parameters (fun column => arithmeticValue inputs (state column)) := by
  exact rounds_evaluate arithmeticOperations (arithmeticValue inputs)
    (arithmetic_evaluates inputs) parameters 65 state

/-- Exact local row certificates for the deployed x^5 chain. Native-only
constant folding is a modular coefficient check, never an honest-value test. -/
inductive FifthCertificate (p : Nat) (rows : List Row) (input output : Linear) : Prop where
  | constant (coefficient : Int)
      (inputEqual : Compiler.canonical p input = Compiler.canonical p [(0, coefficient)])
      (outputEqual : Compiler.canonical p output = Compiler.canonical p [(0, coefficient ^ 5)]) :
      FifthCertificate p rows input output
  | arithmetic (square fourth auxiliary : Linear)
      (squareRow : Compiler.checkRow p rows ⟨input, square⟩ = true)
      (fourthRow : Compiler.checkRow p rows ⟨square, fourth⟩ = true)
      (minusRow : Compiler.checkRow p rows ⟨Compiler.subtract fourth input, auxiliary⟩ = true)
      (plusRow : Compiler.checkRow p rows ⟨fourth ++ input, auxiliary ++ scaleLinear 4 output⟩ = true) :
      FifthCertificate p rows input output

theorem fifth_certificate_sound {p : Nat} [CharP F p] (rho : Nat → F)
    (rows : List Row) (input output : Linear) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) (certificate : FifthCertificate p rows input output) :
    eval rho output = eval rho input ^ 5 := by
  cases certificate with
  | constant coefficient inputEqual outputEqual =>
      have base : eval rho input = (coefficient : F) := by
        simpa only [eval, one, mul_one, add_zero] using
          Compiler.canonical_equal rho input [(0, coefficient)] inputEqual
      have result : eval rho output = (coefficient : F) ^ 5 := by
        simpa only [eval, one, mul_one, add_zero, Int.cast_pow] using
          Compiler.canonical_equal rho output [(0, coefficient ^ 5)] outputEqual
      rw [result, base]
  | arithmetic square fourth auxiliary squareRow fourthRow minusRow plusRow =>
      have first := Compiler.checked_square_sound rho rows input square satisfied squareRow
      have second := Compiler.checked_square_sound rho rows square fourth satisfied fourthRow
      have product := Compiler.checked_product_sound rho rows fourth input output auxiliary
        four satisfied minusRow plusRow
      rw [product, second, first]
      ring

def castParameters {width : Nat} (parameters : Parameters Int width) : Parameters F width :=
  ⟨fun round column => (parameters.ark round column : F),
   fun row column => (parameters.mds row column : F)⟩

def mixLinear {width : Nat} (matrix : Fin width → State Int width)
    (state : State Linear width) : State Linear width := fun row =>
  (List.finRange width).foldl
    (fun total column => total ++ scaleLinear (matrix row column) (state column)) []

theorem eval_linear_fold {I : Type} (rho : Nat → F) (items : List I)
    (coefficient : I → Int) (terms : I → Linear) (initial : Linear) :
    eval rho (items.foldl (fun total i => total ++ scaleLinear (coefficient i) (terms i)) initial) =
      items.foldl (fun total i => total + (coefficient i : F) * eval rho (terms i)) (eval rho initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.foldl_cons, eval_append, eval_scale] using
        ih (initial ++ scaleLinear (coefficient head) (terms head))

/-- Before/after are exact boundary linear expressions. These checks neither
assign existing hash witnesses nor assume any round equation. A generated
composition must match adjacent boundary LCs and the actual requested output;
it must not relabel an unrelated observed expression as a hash state. -/
structure RoundCertificate (p : Nat) (rows : List Row) {width : Nat}
    (parameters : Parameters Int width) (index : Nat)
    (before shifted transformed after : State Linear width) : Prop where
  shift : ∀ column, Compiler.canonical p (shifted column) =
    Compiler.canonical p (before column ++ [(0, parameters.ark index column)])
  nonlinearStep : ∀ column, nonlinear index column.val = true →
    FifthCertificate p rows (shifted column) (transformed column)
  linearStep : ∀ column, nonlinear index column.val = false →
    Compiler.canonical p (transformed column) = Compiler.canonical p (shifted column)
  mix : ∀ row, Compiler.canonical p (after row) =
    Compiler.canonical p (mixLinear parameters.mds transformed row)

theorem round_certificate_sound {p width : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (parameters : Parameters Int width) (index : Nat)
    (before shifted transformed after : State Linear width)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows)
    (certificate : RoundCertificate p rows parameters index before shifted transformed after) :
    (fun column => eval rho (after column)) =
      round (castParameters parameters) index (fun column => eval rho (before column)) := by
  have shiftedValue : ∀ column, eval rho (shifted column) =
      eval rho (before column) + (parameters.ark index column : F) := by
    intro column
    simpa only [eval_append, eval, one, mul_one, add_zero] using
      Compiler.canonical_equal rho _ _ (certificate.shift column)
  have transformedValue : (fun column => eval rho (transformed column)) =
      (fun column => if nonlinear index column.val then
        (eval rho (before column) + (parameters.ark index column : F)) ^ 5
        else eval rho (before column) + (parameters.ark index column : F)) := by
    funext column
    cases active : nonlinear index column.val with
    | false =>
        simpa only [active, Bool.false_eq_true, if_false, shiftedValue] using
          Compiler.canonical_equal rho _ _ (certificate.linearStep column active)
    | true =>
        simpa only [active, if_true, shiftedValue] using
          fifth_certificate_sound rho rows _ _ one four satisfied
            (certificate.nonlinearStep column active)
  funext row
  rw [Compiler.canonical_equal rho _ _ (certificate.mix row)]
  change eval rho ((List.finRange width).foldl
    (fun total column => total ++ scaleLinear (parameters.mds row column) (transformed column)) []) = _
  rw [eval_linear_fold]
  change mix (castParameters parameters).mds (fun column => eval rho (transformed column)) row = _
  rw [transformedValue]
  rfl

/-- Finite round composition over one parameter table. The premise is supplied
by the local checked certificates below, never an assumed hash computation. -/
theorem rounds_chain {width : Nat} (parameters : Parameters F width)
    (states : Nat → State F width) (count : Nat) :
    (∀ index, index < count → states (index + 1) = round parameters index (states index)) →
      states count = rounds parameters count (states 0) := by
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro steps
      rw [steps count (Nat.lt_succ_self count)]
      rw [ih (fun index bound => steps index (Nat.lt_succ_of_lt bound))]
      rfl

/-- Adjacent rounds share exactly the same linear state, not independently
named values. Finite generated certificates check each transition; this
induction does not expand a recursively duplicated arithmetic expression tree. -/
theorem certified_rounds_sound {p width : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (parameters : Parameters Int width)
    (states shifted transformed : Nat → State Linear width) (count : Nat)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows)
    (certificates : ∀ index, index < count → RoundCertificate p rows parameters index
      (states index) (shifted index) (transformed index) (states (index + 1))) :
    (fun column => eval rho (states count column)) =
      rounds (castParameters parameters) count (fun column => eval rho (states 0 column)) := by
  apply rounds_chain (castParameters parameters) (fun index column => eval rho (states index column)) count
  intro index bound
  exact round_certificate_sound rho rows parameters index
    (states index) (shifted index) (transformed index) (states (index + 1))
    one four satisfied (certificates index bound)

def absorbLinear {width : Nat} (state : State Linear width) (chunk : List Linear) : State Linear width :=
  fun column => if column.val = 0 then state column
    else state column ++ chunk[column.val - 1]?.getD []

theorem eval_getD (rho : Nat → F) (chunk : List Linear) (index : Nat) :
    eval rho (chunk[index]?.getD []) = (chunk.map (eval rho))[index]?.getD 0 := by
  induction chunk generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index =>
          change eval rho (tail[index]?.getD []) = (tail.map (eval rho))[index]?.getD 0
          exact ih index

theorem eval_absorbLinear {width : Nat} (rho : Nat → F)
    (state : State Linear width) (chunk : List Linear) :
    (fun column => eval rho (absorbLinear state chunk column)) =
      absorb (fun column => eval rho (state column)) (chunk.map (eval rho)) := by
  funext column
  by_cases zero : column.val = 0
  · simp only [absorbLinear, absorb, zero, if_true]
  · simp only [absorbLinear, absorb, zero, if_false, eval_append, eval_getD]

def initialLinear {width : Nat} (domain arity : Nat) : State Linear width :=
  fun column => if column.val = 0 then [(0, ((arity * 256 + domain : Nat) : Int))] else []

theorem eval_initialLinear {width : Nat} (rho : Nat → F) (one : rho 0 = 1)
    (domain arity : Nat) :
    (fun column => eval rho (initialLinear (width := width) domain arity column)) =
      initial domain arity := by
  funext column
  by_cases zero : column.val = 0
  · simp only [initialLinear, initial, zero, if_true, eval, one, mul_one, add_zero,
      Int.cast_natCast]
  · simp only [initialLinear, initial, zero, if_false, eval]

/-- One actual sponge block: the round-zero LC is checked against additive
absorption of the preceding block's exact state. For a partial block getD []
proves the zero padding; no extra absorption or padding marker is introduced.
The generator separately checks the input list's source order/domain/arity and
the final actual output coordinate. Empty input uses certified_rounds_sound
directly on the initial state, matching sponge's explicit empty branch. -/
theorem certified_block_sound {p width : Nat} [CharP F p]
    (rho : Nat → F) (rows : List Row) (parameters : Parameters Int width)
    (before : State Linear width) (chunk : List Linear)
    (states shifted transformed : Nat → State Linear width)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows)
    (absorption : ∀ column, Compiler.canonical p (states 0 column) =
      Compiler.canonical p (absorbLinear before chunk column))
    (certificates : ∀ index, index < 65 → RoundCertificate p rows parameters index
      (states index) (shifted index) (transformed index) (states (index + 1))) :
    (fun column => eval rho (states 65 column)) =
      permute (castParameters parameters)
        (absorb (fun column => eval rho (before column)) (chunk.map (eval rho))) := by
  have boundary : (fun column => eval rho (states 0 column)) =
      absorb (fun column => eval rho (before column)) (chunk.map (eval rho)) := by
    calc
      _ = (fun column => eval rho (absorbLinear before chunk column)) := by
        funext column
        exact Compiler.canonical_equal rho _ _ (absorption column)
      _ = _ := eval_absorbLinear rho before chunk
  have result := certified_rounds_sound rho rows parameters states shifted transformed
    65 one four satisfied certificates
  simpa only [permute, boundary] using result

#print axioms fifth_evaluates
#print axioms domain_arity_injective
#print axioms round_evaluates
#print axioms rounds_evaluate
#print axioms expected_permutation_evaluates
#print axioms fifth_certificate_sound
#print axioms round_certificate_sound
#print axioms certified_rounds_sound
#print axioms eval_initialLinear
#print axioms certified_block_sound
#print axioms hash6_of_one_block

end ShielddSecurity.Poseidon

set_option pp.all true in
#check @ShielddSecurity.Poseidon.fifth_evaluates

set_option pp.all true in
#check @ShielddSecurity.Poseidon.domain_arity_injective

set_option pp.all true in
#check @ShielddSecurity.Poseidon.round_evaluates

set_option pp.all true in
#check @ShielddSecurity.Poseidon.rounds_evaluate

set_option pp.all true in
#check @ShielddSecurity.Poseidon.expected_permutation_evaluates

set_option pp.all true in
#check @ShielddSecurity.Poseidon.fifth_certificate_sound

set_option pp.all true in
#check @ShielddSecurity.Poseidon.round_certificate_sound

set_option pp.all true in
#check @ShielddSecurity.Poseidon.certified_rounds_sound

set_option pp.all true in
#check @ShielddSecurity.Poseidon.eval_initialLinear

set_option pp.all true in
#check @ShielddSecurity.Poseidon.certified_block_sound

set_option pp.all true in
#check @ShielddSecurity.Poseidon.hash6_of_one_block
