import ShielddSecurity.GroupSubgroupGraphArithmetic
import ShielddSecurity.SourceGraphEvaluation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.GroupSubgroupSourceGraph
open Compiler
open GroupSubgroupGraphArithmetic
variable {F : Type} [Field F]

/-! Expected source program for the closed subgroup cone. The seven input
leaves retain original witness IDs 11--17. Integer constants retain source
representatives; their field interpretations are separate premises. Shape
matching is node syntax and assertion indices, never a desired value equation.
The curve and double blocks have seven and seventeen operations respectively. -/

def constant (d negative : Int) (index : Nat) : Int :=
  if index = 0 then d
  else if index = 1 ∨ index = 4 ∨ index = 8 ∨ index = 12 then negative else 1

def transport {n m : Nat} (equal : n = m) (node : SourceNode n) : SourceNode m :=
  equal ▸ node

theorem transport_value {n m : Nat} (equal : n = m) (node : SourceNode n)
    (inputs : Nat → F) (previous : Fin m → F) :
    sourceValue inputs previous (transport equal node) =
      sourceValue inputs (fun index => previous ⟨index.val, by omega⟩) node := by
  subst m
  rfl

def curveNode (offset : Fin 7) : SourceNode (22 + offset.val) :=
  match offset.val, offset.isLt with
  | 0, _ => .mul ⟨2, by omega⟩ ⟨2, by omega⟩
  | 1, _ => .mul ⟨3, by omega⟩ ⟨3, by omega⟩
  | 2, _ => .mul ⟨8, by omega⟩ ⟨22, by omega⟩
  | 3, _ => .add ⟨23, by omega⟩ ⟨24, by omega⟩
  | 4, _ => .mul ⟨7, by omega⟩ ⟨22, by omega⟩
  | 5, _ => .mul ⟨26, by omega⟩ ⟨23, by omega⟩
  | 6, _ => .add ⟨9, by omega⟩ ⟨27, by omega⟩
  | n + 7, bound => False.elim (by omega)

def doubleNode (phase : Fin 3) (offset : Fin 17) : SourceNode (29 + 17 * phase.val + offset.val) :=
  let start := 29 + 17 * phase.val
  let x := if phase.val = 0 then 2 else 25 + 17 * phase.val
  let y := if phase.val = 0 then 3 else 28 + 17 * phase.val
  match offset.val, offset.isLt with
  | 0, _ => .mul ⟨x, by dsimp [x, start]; split <;> omega⟩ ⟨x, by dsimp [x, start]; split <;> omega⟩
  | 1, _ => .mul ⟨y, by dsimp [y, start]; split <;> omega⟩ ⟨y, by dsimp [y, start]; split <;> omega⟩
  | 2, _ => .mul ⟨start, by omega⟩ ⟨start + 1, by omega⟩
  | 3, _ => .mul ⟨start + 2, by omega⟩ ⟨7, by omega⟩
  | 4, _ => .add ⟨10 + 4 * phase.val, by omega⟩ ⟨start + 3, by omega⟩
  | 5, _ => .mul ⟨11 + 4 * phase.val, by omega⟩ ⟨start + 3, by omega⟩
  | 6, _ => .add ⟨12 + 4 * phase.val, by omega⟩ ⟨start + 5, by omega⟩
  | 7, _ => .mul ⟨start + 4, by omega⟩ ⟨start + 6, by omega⟩
  | 8, _ => .mul ⟨4 + phase.val, by omega⟩ ⟨start + 7, by omega⟩
  | 9, _ => .mul ⟨x, by dsimp [x, start]; split <;> omega⟩ ⟨y, by dsimp [y, start]; split <;> omega⟩
  | 10, _ => .mul ⟨y, by dsimp [y, start]; split <;> omega⟩ ⟨x, by dsimp [x, start]; split <;> omega⟩
  | 11, _ => .add ⟨start + 9, by omega⟩ ⟨start + 10, by omega⟩
  | 12, _ => .mul ⟨start + 11, by omega⟩ ⟨start + 6, by omega⟩
  | 13, _ => .mul ⟨start + 12, by omega⟩ ⟨4 + phase.val, by omega⟩
  | 14, _ => .add ⟨start + 1, by omega⟩ ⟨start, by omega⟩
  | 15, _ => .mul ⟨start + 14, by omega⟩ ⟨start + 4, by omega⟩
  | 16, _ => .mul ⟨start + 15, by omega⟩ ⟨4 + phase.val, by omega⟩
  | n + 17, bound => False.elim (by omega)

def node (d negative : Int) (index : Fin 80) : SourceNode index.val :=
  if input : index.val < 7 then .input (11 + index.val)
  else if leaf : index.val < 22 then .constant (constant d negative (index.val - 7))
  else if curve : index.val < 29 then
    transport (by dsimp; omega) (curveNode ⟨index.val - 22, by omega⟩)
  else
    let phase : Fin 3 := ⟨(index.val - 29) / 17, by omega⟩
    let offset : Fin 17 := ⟨(index.val - 29) % 17, Nat.mod_lt _ (by decide)⟩
    transport (by dsimp [phase, offset]; omega) (doubleNode phase offset)

def assertions : List (Fin 80 × Fin 80) :=
  [(⟨25, by decide⟩, ⟨28, by decide⟩),
   (⟨13, by decide⟩, ⟨37, by decide⟩),
   (⟨17, by decide⟩, ⟨54, by decide⟩),
   (⟨21, by decide⟩, ⟨71, by decide⟩),
   (⟨0, by decide⟩, ⟨76, by decide⟩),
   (⟨1, by decide⟩, ⟨79, by decide⟩)]

def Matches (graph : SourceGraph 22735 80) (d negative : Int) : Prop :=
  (∀ index, graph.node index = node d negative index) ∧ graph.assertions = assertions

theorem modulus_negative_one {p : Nat} [CharP F p] :
    (((p : Int) - 1 : Int) : F) = -1 := by
  simp [Int.cast_sub, CharP.cast_eq_zero F p]

def preimage (inputs : Nat → F) : Group.Point F := ⟨inputs 13, inputs 14⟩
def point (inputs : Nat → F) : Group.Point F := ⟨inputs 11, inputs 12⟩
def hints (inputs : Nat → F) (phase : Nat) : F := inputs (15 + phase)

def reference (d negative : Int) (inputs : Nat → F) (index : Nat) : F :=
  if index < 7 then inputs (11 + index)
  else if index < 22 then (constant d negative (index - 7) : F)
  else if index < 29 then curveValues (d : F) (negative : F) (preimage inputs) (index - 22)
  else doubleValues (d : F) (negative : F)
    (hintTrace (d : F) (preimage inputs) (hints inputs) ((index - 29) / 17))
    (hints inputs ((index - 29) / 17)) ((index - 29) % 17)

theorem reference_input (d negative : Int) (inputs : Nat → F) (offset : Fin 7) :
    reference d negative inputs offset.val = inputs (11 + offset.val) := by
  simp [reference, offset.isLt]

theorem reference_constant (d negative : Int) (inputs : Nat → F) (offset : Fin 15) :
    reference d negative inputs (7 + offset.val) = (constant d negative offset.val : F) := by
  simp [reference, show ¬7 + offset.val < 7 by omega,
    show 7 + offset.val < 22 by omega]

theorem reference_curve (d negative : Int) (inputs : Nat → F) (offset : Fin 7) :
    reference d negative inputs (22 + offset.val) =
      curveValues (d : F) (negative : F) (preimage inputs) offset.val := by
  simp [reference, show ¬22 + offset.val < 7 by omega,
    show ¬22 + offset.val < 22 by omega, show 22 + offset.val < 29 by omega]

theorem reference_double (d negative : Int) (inputs : Nat → F) (phase : Fin 3) (offset : Fin 17) :
    reference d negative inputs (29 + 17 * phase.val + offset.val) =
      doubleValues (d : F) (negative : F)
        (hintTrace (d : F) (preimage inputs) (hints inputs) phase.val)
        (hints inputs phase.val) offset.val := by
  have divided : (17 * phase.val + offset.val) / 17 = phase.val := by
    omega
  have remainder : (17 * phase.val + offset.val) % 17 = offset.val := by omega
  simp [reference, show ¬29 + 17 * phase.val + offset.val < 7 by omega,
    show ¬29 + 17 * phase.val + offset.val < 22 by omega,
    show ¬29 + 17 * phase.val + offset.val < 29 by omega,
    show 29 + 17 * phase.val + offset.val - 29 = 17 * phase.val + offset.val by omega,
    divided, remainder]

theorem reference_previous (d negative : Int) (inputs : Nat → F)
    (negativeOne : (negative : F) = -1) (phase : Fin 3) :
    (⟨reference d negative inputs (if phase.val = 0 then 2 else 25 + 17 * phase.val),
      reference d negative inputs (if phase.val = 0 then 3 else 28 + 17 * phase.val)⟩ : Group.Point F) =
      hintTrace (d : F) (preimage inputs) (hints inputs) phase.val := by
  obtain ⟨count, bound⟩ := phase
  cases count with
  | zero => rfl
  | succ count =>
      simp only [Nat.succ_ne_zero, if_false]
      rw [show 25 + 17 * (count + 1) = 29 + 17 * count + 13 by omega,
        show 28 + 17 * (count + 1) = 29 + 17 * count + 16 by omega]
      rw [reference_double d negative inputs ⟨count, by omega⟩ ⟨13, by decide⟩,
        reference_double d negative inputs ⟨count, by omega⟩ ⟨16, by decide⟩]
      change doubleOutput (d : F) (negative : F) _ _ = _
      rw [negativeOne, double_output_value]
      rfl

theorem reference_phase_constants (d negative : Int) (inputs : Nat → F) (phase : Fin 3) :
    reference d negative inputs (10 + 4 * phase.val) = 1 ∧
    reference d negative inputs (11 + 4 * phase.val) = (negative : F) ∧
    reference d negative inputs (12 + 4 * phase.val) = 1 ∧
    reference d negative inputs (13 + 4 * phase.val) = 1 := by
  fin_cases phase <;> simp [reference, constant]

theorem curve_node_computes (d negative : Int) (inputs : Nat → F) (offset : Fin 7) :
    curveValues (d : F) (negative : F) (preimage inputs) offset.val =
      sourceValue inputs (fun prior => reference d negative inputs prior.val) (curveNode offset) := by
  fin_cases offset <;> simp [curveNode, sourceValue, reference, constant, curveValues, preimage]

theorem double_node_computes (d negative : Int) (inputs : Nat → F)
    (negativeOne : (negative : F) = -1) (phase : Fin 3) (offset : Fin 17) :
    doubleValues (d : F) (negative : F)
        (hintTrace (d : F) (preimage inputs) (hints inputs) phase.val)
        (hints inputs phase.val) offset.val =
      sourceValue inputs (fun prior => reference d negative inputs prior.val) (doubleNode phase offset) := by
  have previous := reference_previous d negative inputs negativeOne phase
  have x : reference d negative inputs (if phase.val = 0 then 2 else 25 + 17 * phase.val) =
      (hintTrace (d : F) (preimage inputs) (hints inputs) phase.val).x := congrArg Group.Point.x previous
  have y : reference d negative inputs (if phase.val = 0 then 3 else 28 + 17 * phase.val) =
      (hintTrace (d : F) (preimage inputs) (hints inputs) phase.val).y := congrArg Group.Point.y previous
  have leaves := reference_phase_constants d negative inputs phase
  have coefficient : reference d negative inputs 7 = (d : F) := by simp [reference, constant]
  have earlier (index : Nat) (bound : index < 17) :=
    reference_double d negative inputs phase ⟨index, bound⟩
  have zeroth : reference d negative inputs (29 + 17 * phase.val) =
      doubleValues (d : F) (negative : F)
        (hintTrace (d : F) (preimage inputs) (hints inputs) phase.val) (hints inputs phase.val) 0 := by
    simpa only [Nat.add_zero] using earlier 0 (by decide)
  have inverseHint : reference d negative inputs (4 + phase.val) = hints inputs phase.val := by
    simp [reference, show 4 + phase.val < 7 by omega, hints]
    congr 1 <;> omega
  fin_cases offset <;>
    dsimp only [doubleNode, sourceValue] <;>
    (try simp only [x, y, leaves.1, leaves.2.1, leaves.2.2.1, inverseHint, coefficient, zeroth,
      earlier 0 (by decide), earlier 1 (by decide), earlier 2 (by decide),
      earlier 3 (by decide), earlier 4 (by decide), earlier 5 (by decide),
      earlier 6 (by decide), earlier 7 (by decide), earlier 9 (by decide),
      earlier 10 (by decide), earlier 11 (by decide), earlier 12 (by decide),
      earlier 14 (by decide), earlier 15 (by decide)]) <;>
    simp only [doubleValues] <;> first | rfl | exact mul_comm _ _

theorem matching_reference_computes (graph : SourceGraph 22735 80) (d negative : Int)
    (inputs : Nat → F) (negativeOne : (negative : F) = -1)
    (shape : Matches graph d negative) (index : Fin 80) :
    reference d negative inputs index.val = sourceValue inputs
      (graph.prior (fun index => reference d negative inputs index.val) index) (graph.node index) := by
  rw [shape.1 index]
  unfold node
  split_ifs with input leaf curve
  · simp [reference, input, sourceValue]
  · simp [reference, input, leaf, sourceValue]
  · rw [transport_value]
    have evaluated : reference d negative inputs index.val =
        curveValues (d : F) (negative : F) (preimage inputs) (index.val - 22) := by
      simp only [reference, input, leaf, curve, ↓reduceIte]
    rw [evaluated]
    exact curve_node_computes d negative inputs ⟨index.val - 22, by omega⟩
  · rw [transport_value]
    have evaluated : reference d negative inputs index.val = doubleValues (d : F) (negative : F)
        (hintTrace (d : F) (preimage inputs) (hints inputs) ((index.val - 29) / 17))
        (hints inputs ((index.val - 29) / 17)) ((index.val - 29) % 17) := by
      simp only [reference, input, leaf, curve, ↓reduceIte]
    rw [evaluated]
    exact double_node_computes d negative inputs negativeOne
      ⟨(index.val - 29) / 17, by omega⟩ ⟨(index.val - 29) % 17, Nat.mod_lt _ (by decide)⟩

theorem matching_evaluation (graph : SourceGraph 22735 80) (d negative : Int)
    (inputs : Nat → F) (negativeOne : (negative : F) = -1)
    (shape : Matches graph d negative) :
    SourceGraphEvaluation.values graph inputs = fun index => reference d negative inputs index.val :=
  SourceGraphEvaluation.computing_values_unique graph inputs _
    (matching_reference_computes graph d negative inputs negativeOne shape)

theorem reference_last (d negative : Int) (inputs : Nat → F)
    (negativeOne : (negative : F) = -1) :
    (⟨reference d negative inputs 76, reference d negative inputs 79⟩ : Group.Point F) =
      hintTrace (d : F) (preimage inputs) (hints inputs) 3 := by
  change (⟨reference d negative inputs (29 + 17 * 2 + 13),
    reference d negative inputs (29 + 17 * 2 + 16)⟩ : Group.Point F) = _
  rw [reference_double d negative inputs ⟨2, by decide⟩ ⟨13, by decide⟩,
    reference_double d negative inputs ⟨2, by decide⟩ ⟨16, by decide⟩]
  change doubleOutput (d : F) (negative : F) _ _ = _
  rw [negativeOne, double_output_value]
  rfl

theorem reference_assertions_iff (d negative : Int) (inputs : Nat → F)
    (negativeOne : (negative : F) = -1) :
    (∀ assertion ∈ assertions,
      reference d negative inputs assertion.1.val = reference d negative inputs assertion.2.val) ↔
      SourceAssertions (d : F) (negative : F) (point inputs) (preimage inputs) (hints inputs) := by
  have last := reference_last d negative inputs negativeOne
  have lastX : reference d negative inputs 76 =
      (hintTrace (d : F) (preimage inputs) (hints inputs) 3).x := congrArg Group.Point.x last
  have lastY : reference d negative inputs 79 =
      (hintTrace (d : F) (preimage inputs) (hints inputs) 3).y := congrArg Group.Point.y last
  simp only [assertions, List.forall_mem_cons]
  simp only [List.not_mem_nil, false_implies, implies_true, forall_const, and_true]
  have curveLeft : reference d negative inputs 25 =
      curveValues (d : F) (negative : F) (preimage inputs) 3 :=
    reference_curve d negative inputs ⟨3, by decide⟩
  have curveRight : reference d negative inputs 28 =
      curveValues (d : F) (negative : F) (preimage inputs) 6 :=
    reference_curve d negative inputs ⟨6, by decide⟩
  have first : reference d negative inputs 37 =
      doubleValues (d : F) (negative : F) (hintTrace (d : F) (preimage inputs) (hints inputs) 0) (hints inputs 0) 8 :=
    reference_double d negative inputs ⟨0, by decide⟩ ⟨8, by decide⟩
  have second : reference d negative inputs 54 =
      doubleValues (d : F) (negative : F) (hintTrace (d : F) (preimage inputs) (hints inputs) 1) (hints inputs 1) 8 :=
    reference_double d negative inputs ⟨1, by decide⟩ ⟨8, by decide⟩
  have third : reference d negative inputs 71 =
      doubleValues (d : F) (negative : F) (hintTrace (d : F) (preimage inputs) (hints inputs) 2) (hints inputs 2) 8 :=
    reference_double d negative inputs ⟨2, by decide⟩ ⟨8, by decide⟩
  rw [curveLeft, curveRight, first, second, third, lastX, lastY]
  have ones : reference d negative inputs 13 = 1 ∧ reference d negative inputs 17 = 1 ∧
      reference d negative inputs 21 = 1 := by simp [reference, constant]
  rw [ones.1, ones.2.1, ones.2.2,
    show reference d negative inputs 0 = inputs 11 from reference_input d negative inputs ⟨0, by decide⟩,
    show reference d negative inputs 1 = inputs 12 from reference_input d negative inputs ⟨1, by decide⟩]
  constructor
  · rintro ⟨curve, first, second, third, x, y⟩
    refine ⟨curve, ?_, x, y⟩
    intro index before
    interval_cases index
    · exact first.symm
    · exact second.symm
    · exact third.symm
  · rintro ⟨curve, inverses, x, y⟩
    exact ⟨curve, (inverses 0 (by decide)).symm, (inverses 1 (by decide)).symm,
      (inverses 2 (by decide)).symm, x, y⟩

theorem graph_assertions_sound (graph : SourceGraph 22735 80) (d negative : Int)
    (inputs : Nat → F) (negativeOne : (negative : F) = -1) (shape : Matches graph d negative)
    (asserted : ∀ assertion ∈ graph.assertions,
      SourceGraphEvaluation.values graph inputs assertion.1 =
        SourceGraphEvaluation.values graph inputs assertion.2) :
    Group.OnCurve (d : F) (preimage inputs) ∧
      GroupNativeCofactor.nativeEight (d : F) (preimage inputs) = point inputs := by
  rw [matching_evaluation graph d negative inputs negativeOne shape, shape.2] at asserted
  exact source_assertions_sound (d : F) (negative : F) _ _ _ negativeOne
    ((reference_assertions_iff d negative inputs negativeOne).mp asserted)

theorem graph_satisfies_sound (graph : SourceGraph 22735 80) (d negative : Int)
    (inputs : Nat → F) (computed : Fin 80 → F)
    (negativeOne : (negative : F) = -1) (shape : Matches graph d negative)
    (satisfied : GraphSatisfies graph inputs computed) :
    Group.OnCurve (d : F) (preimage inputs) ∧
      GroupNativeCofactor.nativeEight (d : F) (preimage inputs) = point inputs := by
  have unique := SourceGraphEvaluation.computing_values_unique graph inputs computed satisfied.1
  exact graph_assertions_sound graph d negative inputs negativeOne shape (by rw [unique]; exact satisfied.2)

def constructedInputs (d : F) (initial : Group.Point F) (remaining : Nat → F) (index : Nat) : F :=
  if index = 11 then (GroupNativeCofactor.nativeEight d initial).x
  else if index = 12 then (GroupNativeCofactor.nativeEight d initial).y
  else if index = 13 then initial.x
  else if index = 14 then initial.y
  else if 15 ≤ index ∧ index < 18 then nativeHints d initial (index - 15)
  else remaining index

theorem constructed_input_roles (d : F) (initial : Group.Point F) (remaining : Nat → F) :
    point (constructedInputs d initial remaining) = GroupNativeCofactor.nativeEight d initial ∧
    preimage (constructedInputs d initial remaining) = initial ∧
    (∀ index < 3, hints (constructedInputs d initial remaining) index = nativeHints d initial index) ∧
    (∀ index, index < 11 ∨ 18 ≤ index → constructedInputs d initial remaining index = remaining index) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [point, constructedInputs]
  · simp [preimage, constructedInputs]
  · intro index before
    simp [hints, constructedInputs, show ¬15 + index = 11 by omega,
      show ¬15 + index = 12 by omega, show ¬15 + index = 13 by omega,
      show ¬15 + index = 14 by omega, show 15 + index < 18 by omega]
  · intro index outside
    simp [constructedInputs, show index ≠ 11 by omega, show index ≠ 12 by omega,
      show index ≠ 13 by omega, show index ≠ 14 by omega, show ¬(15 ≤ index ∧ index < 18) by omega]

theorem hint_trace_congr (d : F) (initial : Group.Point F) (first second : Nat → F) (count : Nat)
    (agree : ∀ index < count, first index = second index) :
    hintTrace d initial first count = hintTrace d initial second count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [hintTrace, previous (by intro index before; exact agree index (by omega)), agree count (by omega)]

theorem graph_assertions_complete (graph : SourceGraph 22735 80) (d negative : Int)
    (initial : Group.Point F) (remaining : Nat → F)
    (negativeOne : (negative : F) = -1) (shape : Matches graph d negative)
    (valid : Group.OnCurve (d : F) initial)
    (denominators : ∀ index < 3, inverseProduct (d : F) (nativeTrace (d : F) initial index) ≠ 0) :
    let inputs := constructedInputs (d : F) initial remaining
    ∀ assertion ∈ graph.assertions,
      SourceGraphEvaluation.values graph inputs assertion.1 =
        SourceGraphEvaluation.values graph inputs assertion.2 := by
  dsimp only
  rw [matching_evaluation graph d negative _ negativeOne shape, shape.2]
  apply (reference_assertions_iff d negative _ negativeOne).mpr
  have roles := constructed_input_roles (d : F) initial remaining
  have trace (count : Nat) (before : count ≤ 3) :
      hintTrace (d : F) initial (hints (constructedInputs (d : F) initial remaining)) count =
        hintTrace (d : F) initial (nativeHints (d : F) initial) count :=
    hint_trace_congr _ _ _ _ _ (by intro index prior; exact roles.2.2.1 index (by omega))
  have complete := source_assertions_complete (d : F) (negative : F) initial negativeOne valid denominators
  unfold SourceAssertions
  rw [roles.1, roles.2.1]
  refine ⟨complete.1, ?_, ?_, ?_⟩
  · intro index before
    rw [trace index (by omega), roles.2.2.1 index before]
    exact complete.2.1 index before
  · rw [trace 3 (by decide)]
    exact complete.2.2.1
  · rw [trace 3 (by decide)]
    exact complete.2.2.2

def groupTrace {J : Type} [AddCommGroup J] (initial : J) : Nat → J
  | 0 => initial
  | count + 1 => groupTrace initial count + groupTrace initial count

theorem native_trace_coordinates {J : Type} [AddCommGroup J] (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (initial : J) (count : Nat) :
    nativeTrace d (model.coordinates initial) count = model.coordinates (groupTrace initial count) := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [nativeTrace, previous, groupTrace]
      exact GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare _ _

theorem native_preimage_denominators [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0) (initial : J) :
    ∀ index < 3, inverseProduct d
      (nativeTrace d (GroupNativeCofactor.nativePreimage d codec writer (model.coordinates initial)) index) ≠ 0 := by
  intro index before
  rw [GroupNativeCofactor.native_preimage_coordinates codec writer d imaginary model nonSquare
    imaginarySquare two initial,
    native_trace_coordinates d imaginary model nonSquare imaginarySquare]
  have nonzero := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    (model.coordinates (groupTrace (GroupNativeCofactor.inverseEight • initial) index))
    (model.coordinates (groupTrace (GroupNativeCofactor.inverseEight • initial) index))
    (model.onCurve _) (model.onCurve _)
  exact mul_ne_zero nonzero.1 nonzero.2

/-- The independently admitted subgroup point constructs the preimage and
three inverse hints. Identity points are allowed here. The named codec,
curve-model and field contracts remain explicit; this is not a deployed
cryptographic instance or an original-row completion theorem. -/
theorem native_graph_assertions_complete [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (graph : SourceGraph 22735 80) (d negative : Int)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (imaginary : F) (model : Group.StandardCurveModel J (d : F))
    (negativeOne : (negative : F) = -1) (shape : Matches graph d negative)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (initial : J) (subgroup : Scalar.order • initial = 0)
    (remaining : Nat → F) :
    let q := GroupNativeCofactor.nativePreimage (d : F) codec writer (model.coordinates initial)
    let inputs := constructedInputs (d : F) q remaining
    point inputs = model.coordinates initial ∧ preimage inputs = q ∧
      ∀ assertion ∈ graph.assertions,
        SourceGraphEvaluation.values graph inputs assertion.1 =
          SourceGraphEvaluation.values graph inputs assertion.2 := by
  dsimp only
  have complete := GroupNativeCofactor.native_preimage_complete codec writer (d : F) imaginary model
    nonSquare imaginarySquare two initial subgroup
  have roles := constructed_input_roles (d : F)
    (GroupNativeCofactor.nativePreimage (d : F) codec writer (model.coordinates initial)) remaining
  exact ⟨roles.1.trans complete.2, roles.2.1,
    graph_assertions_complete graph d negative _ remaining negativeOne shape complete.1
      (native_preimage_denominators codec writer (d : F) imaginary model nonSquare imaginarySquare two initial)⟩

end ShielddSecurity.GroupSubgroupSourceGraph
