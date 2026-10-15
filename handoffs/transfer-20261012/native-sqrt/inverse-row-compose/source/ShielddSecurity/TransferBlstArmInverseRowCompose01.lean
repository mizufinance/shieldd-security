import ShielddSecurity.TransferBlstArmInverseTailCapacity01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowCompose01

/-! Small exact linear-row composition. This is the algebra used to carry
source sign-corrected batch rows across the fixed schedule. Source row
production, coefficient bounds and compiled word operations are separate. -/

structure SourceLinearRows where
  f0 : Int
  g0 : Int
  f1 : Int
  g1 : Int

def sourceIdentityRows : SourceLinearRows := ⟨1, 0, 0, 1⟩

def sourceComposeRows (previous next : SourceLinearRows) : SourceLinearRows :=
  ⟨next.f0 * previous.f0 + next.g0 * previous.f1,
   next.f0 * previous.g0 + next.g0 * previous.g1,
   next.f1 * previous.f0 + next.g1 * previous.f1,
   next.f1 * previous.g0 + next.g1 * previous.g1⟩

def SourceLinearTracks (inputA inputB scale valueA valueB : Int) (rows : SourceLinearRows) : Prop :=
  scale * valueA = rows.f0 * inputA + rows.g0 * inputB ∧
    scale * valueB = rows.f1 * inputA + rows.g1 * inputB

theorem the_identity_rows_track_both_original_inputs_at_scale_one
    (inputA inputB : Int) : SourceLinearTracks inputA inputB 1 inputA inputB sourceIdentityRows := by
  constructor
  · change 1 * inputA = 1 * inputA + 0 * inputB
    simp only [Int.one_mul, Int.zero_mul, Int.add_zero]
  · change 1 * inputB = 0 * inputA + 1 * inputB
    simp only [Int.one_mul, Int.zero_mul, Int.zero_add]

theorem one_next_exact_row_composes_both_previous_exact_input_rows
    (inputA inputB valueA valueB result scale radix oldF0 oldG0 oldF1 oldG1 nextF nextG : Int)
    (left : scale * valueA = oldF0 * inputA + oldG0 * inputB)
    (right : scale * valueB = oldF1 * inputA + oldG1 * inputB)
    (next : radix * result = nextF * valueA + nextG * valueB) :
    (scale * radix) * result =
      (nextF * oldF0 + nextG * oldF1) * inputA + (nextF * oldG0 + nextG * oldG1) * inputB := by
  calc
    _ = scale * (radix * result) := Int.mul_assoc _ _ _
    _ = scale * (nextF * valueA + nextG * valueB) := congrArg (fun x : Int => scale * x) next
    _ = nextF * (scale * valueA) + nextG * (scale * valueB) := by ring1
    _ = nextF * (oldF0 * inputA + oldG0 * inputB) + nextG * (oldF1 * inputA + oldG1 * inputB) := by rw [left, right]
    _ = _ := by ring1

theorem two_exact_linear_row_steps_compose_at_the_product_of_their_scales
    (inputA inputB valueA valueB resultA resultB scale radix : Int)
    (previous next : SourceLinearRows)
    (old : SourceLinearTracks inputA inputB scale valueA valueB previous)
    (step : SourceLinearTracks valueA valueB radix resultA resultB next) :
    SourceLinearTracks inputA inputB (scale * radix) resultA resultB (sourceComposeRows previous next) := by
  constructor
  · exact one_next_exact_row_composes_both_previous_exact_input_rows _ _ _ _ _ _ _ _ _ _ _ _ _ old.1 old.2 step.1
  · exact one_next_exact_row_composes_both_previous_exact_input_rows _ _ _ _ _ _ _ _ _ _ _ _ _ old.1 old.2 step.2

set_option pp.all true in
#check @SourceLinearRows
#print axioms SourceLinearRows
set_option pp.all true in
#check @sourceIdentityRows
#print axioms sourceIdentityRows
set_option pp.all true in
#check @sourceComposeRows
#print axioms sourceComposeRows
set_option pp.all true in
#check @SourceLinearTracks
#print axioms SourceLinearTracks
set_option pp.all true in
#check @the_identity_rows_track_both_original_inputs_at_scale_one
#print axioms the_identity_rows_track_both_original_inputs_at_scale_one
set_option pp.all true in
#check @one_next_exact_row_composes_both_previous_exact_input_rows
#print axioms one_next_exact_row_composes_both_previous_exact_input_rows
set_option pp.all true in
#check @two_exact_linear_row_steps_compose_at_the_product_of_their_scales
#print axioms two_exact_linear_row_steps_compose_at_the_product_of_their_scales
end ShielddSecurity.TransferBlstArmInverseRowCompose01
