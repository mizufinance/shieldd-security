import ShielddSecurity.GroupVariableCircuitNative
import ShielddSecurity.RowRenaming

set_option maxHeartbeats 300000
set_option maxRecDepth 2048

namespace ShielddSecurity.GroupCircuitRenaming

open GroupCircuitCompletion
variable {F : Type} [Field F]

/-- Rename the exact lowered constructor, retaining coefficients and order.
Actual applications separately bind its original physical rows and source roles. -/
def compilerStep (columns : Nat → Nat) : CompilerCompletion.Step → CompilerCompletion.Step
  | .square input remainder output =>
      .square (RowRenaming.linear columns input) (RowRenaming.linear columns remainder) (columns output)
  | .product left right remainder output auxiliary =>
      .product (RowRenaming.linear columns left) (RowRenaming.linear columns right)
        (RowRenaming.linear columns remainder) (columns output) (columns auxiliary)
  | .equal left right => .equal (RowRenaming.linear columns left) (RowRenaming.linear columns right)
  | .squareEqual input target => .squareEqual (RowRenaming.linear columns input) (RowRenaming.linear columns target)

def step (columns : Nat → Nat) : Step → Step
  | .compiler source => .compiler (compilerStep columns source)
  | .quotient numerator denominator remainder quotient product auxiliary =>
      .quotient (RowRenaming.linear columns numerator) (RowRenaming.linear columns denominator)
        (RowRenaming.linear columns remainder) (columns quotient) (columns product) (columns auxiliary)
  | .linear input remainder output =>
      .linear (RowRenaming.linear columns input) (RowRenaming.linear columns remainder) (columns output)

/-- Global injection is a syntactic column-map obligation, never a field or
point value premise. A finite permutation instance supplies it independently. -/
theorem step_commutes (columns : Nat → Nat) (injective : Function.Injective columns)
    (base : Nat → F) (source : Step) (column : Nat) :
    (step columns source).run base (columns column) =
      source.run (fun item => base (columns item)) column := by
  have equality (left right : Nat) : columns left = columns right ↔ left = right :=
    ⟨fun h => injective h, congrArg columns⟩
  cases source with
  | compiler source =>
      cases source <;>
        simp only [step,compilerStep,Step.run,CompilerCompletion.Step.run,
          CompilerCompletion.extendSquare,ScalarCompletion.extendProduct,
          ScalarCompletion.productValues,patchAssignment,List.mem_cons,List.mem_singleton,
          List.not_mem_nil,or_false,RowRenaming.eval_linear,equality]
  | quotient numerator denominator remainder quotient product auxiliary =>
      simp only [step,Step.run,GroupRowCompletion.extendQuotient,
        GroupRowCompletion.quotientValues,GroupRowCompletion.writes,patchAssignment,
        List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
        RowRenaming.eval_linear,equality]
  | linear input remainder output =>
      simp only [step,Step.run,CompilerLinearCompletion.extend,patchAssignment,
        List.mem_singleton,RowRenaming.eval_linear,equality]

/-- Symbolic list induction transports the assignment itself. Thus reusing a
local constructor does not assume that target rows or endpoints already hold. -/
theorem run_commutes (columns : Nat → Nat) (injective : Function.Injective columns)
    (base : Nat → F) (sources : List Step) :
    (fun column => run base (sources.map (step columns)) (columns column)) =
      run (fun column => base (columns column)) sources := by
  induction sources generalizing base with
  | nil => rfl
  | cons source tail ih =>
      simp only [List.map_cons,run]
      rw [ih]
      have same : (fun column => (step columns source).run base (columns column)) =
          source.run (fun column => base (columns column)) := by
        funext column
        exact step_commutes columns injective base source column
      rw [same]

theorem point_commutes (columns : Nat → Nat) (injective : Function.Injective columns)
    (base : Nat → F) (sources : List Step) (point : Linear × Linear) :
    GroupFixedCircuitCompletion.point (run base (sources.map (step columns)))
      (RowRenaming.linear columns point.1,RowRenaming.linear columns point.2) =
    GroupFixedCircuitCompletion.point (run (fun column => base (columns column)) sources) point := by
  simp only [GroupFixedCircuitCompletion.point,RowRenaming.eval_linear,
    run_commutes columns injective base sources]

/-- The instance supplies source truth by invoking its universal constructor,
and supplies exact target coverage from actual retained original rows. No
native meaning or output equality is inferred from a digest or this lemma. -/
theorem rows_complete (columns : Nat → Nat) (injective : Function.Injective columns)
    (base : Nat → F) (sources : List Step) (original actual : List Row)
    (coverage : ∀ target ∈ actual, ∃ source ∈ original, RowRenaming.row columns source = target)
    (constructed : Satisfies (run (fun column => base (columns column)) sources) original) :
    Satisfies (run base (sources.map (step columns))) actual := by
  intro target member
  obtain ⟨source,present,rfl⟩ := coverage target member
  change Square
    (eval (run base (sources.map (step columns))) (RowRenaming.linear columns source.a))
    (eval (run base (sources.map (step columns))) (RowRenaming.linear columns source.b))
  rw [RowRenaming.eval_linear,RowRenaming.eval_linear,run_commutes columns injective base sources]
  exact constructed source present

def program (columns : Nat → Nat) (source : GroupFixedCircuitCompletion.Program) :
    GroupFixedCircuitCompletion.Program :=
  ⟨source.stages.map (step columns),source.rows.map (RowRenaming.row columns),
    (RowRenaming.linear columns source.input.1,RowRenaming.linear columns source.input.2),
    (RowRenaming.linear columns source.output.1,RowRenaming.linear columns source.output.2),
    RowRenaming.linear columns source.low,RowRenaming.linear columns source.high,
    source.lowBit,source.highBit⟩

def tables (columns : Nat → Nat) (source : GroupVariableCircuitCompletion.Tables) :
    GroupVariableCircuitCompletion.Tables :=
  ⟨(RowRenaming.linear columns source.base.1,RowRenaming.linear columns source.base.2),
    (RowRenaming.linear columns source.twice.1,RowRenaming.linear columns source.twice.2),
    (RowRenaming.linear columns source.triple.1,RowRenaming.linear columns source.triple.2)⟩

private theorem point_pullback (base : Nat → F) (columns : Nat → Nat) (coordinates : Linear × Linear) :
    GroupFixedCircuitCompletion.point base
      (RowRenaming.linear columns coordinates.1,RowRenaming.linear columns coordinates.2) =
    GroupFixedCircuitCompletion.point (fun column => base (columns column)) coordinates := by
  simp only [GroupFixedCircuitCompletion.point,RowRenaming.eval_linear]

/-- Reuse a proved universal local constructor, with no desired target
satisfaction or coordinate hypothesis. Injection and fixed original constants
are syntactic obligations of the actual finite column permutation. -/
theorem local_constructor (columns : Nat → Nat) (injective : Function.Injective columns)
    (zero : columns 0 = 0) (copy : Nat) (copyFixed : columns copy = copy)
    (d : F) (sourceTables : GroupVariableCircuitCompletion.Tables)
    (source : GroupFixedCircuitCompletion.Program)
    (sourceConstructs : GroupVariableCircuitCompletion.LocalConstruct d copy sourceTables source) :
    GroupVariableCircuitCompletion.LocalConstruct d copy (tables columns sourceTables) (program columns source) := by
  intro base one linked incoming curved low high
  have sourceOne : (fun column => base (columns column)) 0 = 1 := by simpa only [zero] using one
  have sourceLink : (fun column => base (columns column)) copy =
      (fun column => base (columns column)) 0 := by simpa only [zero,copyFixed] using linked
  have sourceIncoming : Group.OnCurve d
      (GroupFixedCircuitCompletion.point (fun column => base (columns column)) source.input) := by
    simpa only [program,point_pullback] using incoming
  have sourceTablesCurved : GroupVariableCircuitCompletion.Curved d sourceTables
      (fun column => base (columns column)) := by
    simpa only [tables,GroupVariableCircuitCompletion.Curved,point_pullback] using curved
  have sourceLow : eval (fun column => base (columns column)) source.low =
      if source.lowBit then 1 else 0 := by simpa only [program,RowRenaming.eval_linear] using low
  have sourceHigh : eval (fun column => base (columns column)) source.high =
      if source.highBit then 1 else 0 := by simpa only [program,RowRenaming.eval_linear] using high
  have completed := sourceConstructs _ sourceOne sourceLink sourceIncoming sourceTablesCurved sourceLow sourceHigh
  constructor
  · apply rows_complete columns injective base source.stages source.rows
      (source.rows.map (RowRenaming.row columns))
    · intro target member
      exact List.mem_map.mp member
    · exact completed.1
  · simpa only [program,GroupFixedCircuitCompletion.Program.build,
      point_commutes columns injective base source.stages source.output] using completed.2

theorem local_formula (columns : Nat → Nat) (injective : Function.Injective columns)
    (zero : columns 0 = 0) (copy : Nat) (copyFixed : columns copy = copy)
    (d : F) (sourceTables : GroupVariableCircuitCompletion.Tables)
    (source : GroupFixedCircuitCompletion.Program)
    (formula : GroupVariableCircuitNative.LocalFormula d copy sourceTables source) :
    GroupVariableCircuitNative.LocalFormula d copy (tables columns sourceTables) (program columns source) := by
  intro base one linked incoming curved low high
  have sourceOne : (fun column => base (columns column)) 0 = 1 := by simpa only [zero] using one
  have sourceLink : (fun column => base (columns column)) copy =
      (fun column => base (columns column)) 0 := by simpa only [zero,copyFixed] using linked
  have sourceIncoming : Group.OnCurve d
      (GroupFixedCircuitCompletion.point (fun column => base (columns column)) source.input) := by
    simpa only [program,point_pullback] using incoming
  have sourceTablesCurved : GroupVariableCircuitCompletion.Curved d sourceTables
      (fun column => base (columns column)) := by
    simpa only [tables,GroupVariableCircuitCompletion.Curved,point_pullback] using curved
  have sourceLow : eval (fun column => base (columns column)) source.low =
      if source.lowBit then 1 else 0 := by simpa only [program,RowRenaming.eval_linear] using low
  have sourceHigh : eval (fun column => base (columns column)) source.high =
      if source.highBit then 1 else 0 := by simpa only [program,RowRenaming.eval_linear] using high
  have completed := formula _ sourceOne sourceLink sourceIncoming sourceTablesCurved sourceLow sourceHigh
  simpa only [program,tables,GroupFixedCircuitCompletion.Program.build,
    point_commutes columns injective base source.stages source.output,
    point_pullback,RowRenaming.eval_linear] using completed

set_option pp.all true in
#check @step_commutes
#print axioms step_commutes
set_option pp.all true in
#check @run_commutes
#print axioms run_commutes
set_option pp.all true in
#check @point_commutes
#print axioms point_commutes
set_option pp.all true in
#check @rows_complete
#print axioms rows_complete
set_option pp.all true in
#check @local_constructor
#print axioms local_constructor
set_option pp.all true in
#check @local_formula
#print axioms local_formula

end ShielddSecurity.GroupCircuitRenaming
