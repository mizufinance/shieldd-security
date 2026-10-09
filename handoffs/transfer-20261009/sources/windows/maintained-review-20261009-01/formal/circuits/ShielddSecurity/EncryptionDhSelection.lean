import ShielddSecurity.GroupWindows

set_option maxHeartbeats 200000

namespace ShielddSecurity.EncryptionDhSelection

/-- The owned two-coordinate selector, before using its Boolean rows. -/
def select {F : Type} [Field F] (flag : F) (detection payload : Group.Point F) : Group.Point F :=
  ⟨payload.x + flag * (detection.x - payload.x),
    payload.y + flag * (detection.y - payload.y)⟩

theorem select_zero {F : Type} [Field F] (detection payload : Group.Point F) :
    select (0 : F) detection payload = payload := by
  cases payload
  simp only [select, zero_mul, add_zero]

theorem select_one {F : Type} [Field F] (detection payload : Group.Point F) :
    select (1 : F) detection payload = detection := by
  cases detection
  cases payload
  simp only [select, one_mul]
  congr 1 <;> ring

/-- Source arithmetic becomes a branch only after deriving Booleanity. -/
theorem boolean_selection {F : Type} [Field F] [DecidableEq F] (flag : F) (detection payload : Group.Point F)
    (boolean : flag = 0 ∨ flag = 1) :
    select flag detection payload = if flag = 1 then detection else payload := by
  rcases boolean with zero | one
  · subst flag
    simpa using select_zero detection payload
  · subst flag
    simpa using select_one detection payload

/-- Standard curve coordinates preserve the actual selected base operand.
The actual source/row certificate must instantiate this selector expression. -/
theorem represented_selection {F J : Type} [Field F] [DecidableEq F] [AddCommGroup J] {d : F}
    (model : Group.StandardCurveModel J d) (flag : F) (detection payload : J)
    (boolean : flag = 0 ∨ flag = 1) :
    select flag (model.coordinates detection) (model.coordinates payload) =
      model.coordinates (if flag = 1 then detection else payload) := by
  rw [boolean_selection flag _ _ boolean]
  by_cases branch : flag = 1 <;> simp [branch]

set_option pp.all true in
#check @select_zero
#print axioms select_zero
set_option pp.all true in
#check @select_one
#print axioms select_one
set_option pp.all true in
#check @boolean_selection
#print axioms boolean_selection
set_option pp.all true in
#check @represented_selection
#print axioms represented_selection

end ShielddSecurity.EncryptionDhSelection
