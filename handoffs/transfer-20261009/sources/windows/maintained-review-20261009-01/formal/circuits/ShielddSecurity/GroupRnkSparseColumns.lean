import ShielddSecurity.GroupSparseRenamingSequence

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupRnkSparseColumns

/-- The candidate map becomes an actual row map only after exact original-row
coverage. The interval facts below describe this function, not compiler origin. -/
def columns (column : Nat) : Nat :=
  if 1504 ≤ column ∧ column ≤ 1505 then column + 16
  else if 2253 ≤ column ∧ column ≤ 3008 then column + 756
  else if 51214 ≤ column ∧ column ≤ 55994 then column + 4781
  else column

def Owned (column : Nat) : Prop :=
  (2253 ≤ column ∧ column ≤ 3008) ∨ (51214 ≤ column ∧ column ≤ 55994)

private theorem low_value (column : Nat) (lower : 2253 ≤ column) (upper : column ≤ 3008) :
    columns column = column + 756 := by
  have before : ¬ (1504 ≤ column ∧ column ≤ 1505) := by omega
  have inside : 2253 ≤ column ∧ column ≤ 3008 := ⟨lower,upper⟩
  simp only [columns,if_neg before,if_pos inside]

private theorem high_value (column : Nat) (lower : 51214 ≤ column) (upper : column ≤ 55994) :
    columns column = column + 4781 := by
  have before : ¬ (1504 ≤ column ∧ column ≤ 1505) := by omega
  have low : ¬ (2253 ≤ column ∧ column ≤ 3008) := by omega
  have inside : 51214 ≤ column ∧ column ≤ 55994 := ⟨lower,upper⟩
  simp only [columns,if_neg before,if_neg low,if_pos inside]

theorem owned_image_bounds (column : Nat) (owned : Owned column) :
    (3009 ≤ columns column ∧ columns column ≤ 3764) ∨
    (55995 ≤ columns column ∧ columns column ≤ 60775) := by
  rcases owned with ⟨lower,upper⟩ | ⟨lower,upper⟩
  · rw [low_value column lower upper]
    omega
  · rw [high_value column lower upper]
    omega

/-- Restricted to the complete reviewed write ranges. No global injectivity
is asserted: unrelated columns can collide with mapped owned columns. -/
theorem owned_injective (left right : Nat) (leftOwned : Owned left) (rightOwned : Owned right)
    (equal : columns left = columns right) : left = right := by
  rcases leftOwned with ⟨ll,lu⟩ | ⟨ll,lu⟩ <;>
    rcases rightOwned with ⟨rl,ru⟩ | ⟨rl,ru⟩
  · rw [low_value left ll lu,low_value right rl ru] at equal
    omega
  · rw [low_value left ll lu,high_value right rl ru] at equal
    omega
  · rw [high_value left ll lu,low_value right rl ru] at equal
    omega
  · rw [high_value left ll lu,high_value right rl ru] at equal
    omega

/-- Source constants, native input coordinates, and252 shared bit columns are
checked to lie below2253; the retained constant-copy column lies above60775.
Their mapped supports avoid every write image across all bounded patches. -/
theorem independent_outside (column write : Nat)
    (independent : column < 2253 ∨ 60775 < column) (owned : Owned write) :
    columns column ≠ columns write := by
  have bounds := owned_image_bounds write owned
  have columnBounds : columns column < 3009 ∨ 60775 < columns column := by
    by_cases first : 1504 ≤ column ∧ column ≤ 1505
    · simp only [columns,if_pos first]
      omega
    · by_cases low : 2253 ≤ column ∧ column ≤ 3008
      · simp only [columns,if_neg first,if_pos low]
        omega
      · by_cases high : 51214 ≤ column ∧ column ≤ 55994
        · simp only [columns,if_neg first,if_neg low,if_pos high]
          omega
        · simp only [columns,if_neg first,if_neg low,if_neg high]
          omega
  intro equal
  rw [equal] at columnBounds
  omega

set_option pp.all true in
#check @owned_image_bounds
#print axioms owned_image_bounds
set_option pp.all true in
#check @owned_injective
#print axioms owned_injective
set_option pp.all true in
#check @independent_outside
#print axioms independent_outside

end ShielddSecurity.GroupRnkSparseColumns
