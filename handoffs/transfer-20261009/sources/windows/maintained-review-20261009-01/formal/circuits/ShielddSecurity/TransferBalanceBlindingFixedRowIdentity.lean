import ShielddSecurity.RuntimeBalanceBlindingTemplateScalarSoundness

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferBalanceBlindingFixedRowIdentity

/-- Row concatenation is proved symbolically, without evaluating physical rows. -/
theorem program_rows_append (left right : List GroupFixedCircuitCompletion.Program) :
    GroupFixedCircuitCompletion.rows (left ++ right) =
      GroupFixedCircuitCompletion.rows left ++ GroupFixedCircuitCompletion.rows right := by
  induction left with
  | nil => rfl
  | cons program tail ih =>
      simp only [List.cons_append, GroupFixedCircuitCompletion.rows, ih, List.append_assoc]

theorem page_rows_flatten (pages : List (List GroupFixedTemplateTrace.Window)) :
    GroupFixedCircuitCompletion.rows (pages.flatten.map GroupFixedTemplateTrace.Window.program) =
      (pages.map (fun page => GroupFixedCircuitCompletion.rows
        (page.map GroupFixedTemplateTrace.Window.program))).flatten := by
  induction pages with
  | nil => rfl
  | cons page tail ih =>
      simp only [List.flatten_cons, List.map_append, program_rows_append, ih, List.map_cons]

theorem page00_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage00Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage00Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page01_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage01Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage01Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page02_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage02Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage02Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page03_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage03Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage03Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page04_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage04Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage04Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page05_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage05Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage05Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page06_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage06Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage06Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

theorem page07_rows (n : Nat) :
    GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage07Trace.windows n).map GroupFixedTemplateTrace.Window.program) =
      GroupFixedCircuitCompletion.rows ((RuntimeBalanceBlindingTemplatePage07Trace.windows 0).map GroupFixedTemplateTrace.Window.program) := by
  rfl

/-- Scalar-dependent witness labels leave every physical constraint unchanged. -/
theorem rows_independent (n : Nat) :
    RuntimeBalanceBlindingTemplateScalarSoundness.rows n =
      RuntimeBalanceBlindingTemplateScalarSoundness.rows 0 := by
  simp only [RuntimeBalanceBlindingTemplateScalarSoundness.rows,
    RuntimeBalanceBlindingTemplateOrdinaryTrace.windows, page_rows_flatten,
    RuntimeBalanceBlindingTemplateOrdinaryTrace.pages, List.map_cons, List.map_nil,
    page00_rows, page01_rows, page02_rows, page03_rows, page04_rows, page05_rows, page06_rows, page07_rows]

/-- The output column pair is fixed by the source, independently of its bits. -/
theorem endpoint_independent (n : Nat) :
    GroupFixedTemplateTrace.endpoint RuntimeBalanceBlindingTemplateOrdinaryTrace.input
      (RuntimeBalanceBlindingTemplateOrdinaryTrace.windows n) =
    GroupFixedTemplateTrace.endpoint RuntimeBalanceBlindingTemplateOrdinaryTrace.input
      (RuntimeBalanceBlindingTemplateOrdinaryTrace.windows 0) := by
  rfl

set_option pp.all true in
#check @page00_rows
#print axioms page00_rows
set_option pp.all true in
#check @page01_rows
#print axioms page01_rows
set_option pp.all true in
#check @page02_rows
#print axioms page02_rows
set_option pp.all true in
#check @page03_rows
#print axioms page03_rows
set_option pp.all true in
#check @page04_rows
#print axioms page04_rows
set_option pp.all true in
#check @page05_rows
#print axioms page05_rows
set_option pp.all true in
#check @page06_rows
#print axioms page06_rows
set_option pp.all true in
#check @page07_rows
#print axioms page07_rows
set_option pp.all true in
#check @program_rows_append
#print axioms program_rows_append
set_option pp.all true in
#check @page_rows_flatten
#print axioms page_rows_flatten
set_option pp.all true in
#check @rows_independent
#print axioms rows_independent
set_option pp.all true in
#check @endpoint_independent
#print axioms endpoint_independent

end ShielddSecurity.TransferBalanceBlindingFixedRowIdentity
