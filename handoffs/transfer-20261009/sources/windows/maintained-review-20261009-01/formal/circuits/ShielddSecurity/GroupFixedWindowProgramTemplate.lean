import ShielddSecurity.GroupFixedWindowTemplate
import ShielddSecurity.GroupCircuitSequenceCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupFixedWindowProgramTemplate

variable {F : Type} [Field F]

/-- Transport the exact material-only compiler list into the mixed stage
interpreter used by the existing symbolic fixed-loop constructor. -/
theorem compiler_run (base : Nat → F) (steps : List CompilerCompletion.Step) :
    GroupCircuitCompletion.run base (steps.map GroupCircuitCompletion.Step.compiler) =
      CompilerCompletion.run base steps := by
  induction steps generalizing base with
  | nil => rfl
  | cons step tail ih =>
      simpa only [List.map_cons,GroupCircuitCompletion.run,GroupCircuitCompletion.Step.run,
        CompilerCompletion.run] using ih (step.run base)

def quotientStep (coordinate : GroupQuotientPairCompletion.Coordinate) : GroupCircuitCompletion.Step :=
  .quotient coordinate.numerator coordinate.denominator coordinate.remainder
    coordinate.output coordinate.product coordinate.auxiliary

def stages (material : List CompilerCompletion.Step)
    (x y : GroupQuotientPairCompletion.Coordinate) : List GroupCircuitCompletion.Step :=
  material.map GroupCircuitCompletion.Step.compiler ++ [quotientStep x,quotientStep y]

/-- Definitional source-order association, not an output-coordinate premise.
The same constructed assignment can enter GroupFixedCircuitCompletion's
symbolic126 program list without replaying the six product proofs per window. -/
theorem mixed_run (base : Nat → F) (material : List CompilerCompletion.Step)
    (x y : GroupQuotientPairCompletion.Coordinate) :
    GroupCircuitCompletion.run base (stages material x y) =
      GroupFixedWindowTemplate.construct base material x y := by
  rw [stages,GroupCircuitSequenceCompletion.run_append,compiler_run]
  rfl

set_option pp.all true in
#check @compiler_run
#print axioms compiler_run
set_option pp.all true in
#check @mixed_run
#print axioms mixed_run

end ShielddSecurity.GroupFixedWindowProgramTemplate
