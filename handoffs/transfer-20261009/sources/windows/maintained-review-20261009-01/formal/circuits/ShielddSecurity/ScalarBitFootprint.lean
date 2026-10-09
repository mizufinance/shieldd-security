import ShielddSecurity.ScalarRandomizerBounds

set_option maxHeartbeats 100000

namespace ShielddSecurity.ScalarBitFootprint

theorem weighted_below (bound : Nat) (columns : List Nat) (weight : Int)
    (below : ∀ column ∈ columns, column < bound) :
    ScalarRandomizerBounds.LinearBelow bound (weighted columns weight) := by
  induction columns generalizing weight with
  | nil => intro term member; cases member
  | cons column tail ih =>
      intro term member
      simp only [weighted,List.mem_cons] at member
      rcases member with rfl | member
      · exact below column (by simp)
      · exact ih (weight * 2)
          (by intro next member; exact below next (List.mem_cons_of_mem _ member)) term member

/-- The same symbolic footprint applies to actual4,252 and255-bit blocks.
This is only support coverage; no value or reconstruction truth is assumed. -/
theorem initial_rows_below (value start width upper : Nat) (valueBelow : value < upper)
    (bitsBelow : (List.range' start width).all (fun column => decide (column < upper)) = true) :
    ScalarRandomizerBounds.RowsBelow upper
      ((List.range' start width).map booleanRow ++ [reconstructionRow value (List.range' start width)]) := by
  have columns : ∀ column ∈ List.range' start width, column < upper := by
    intro column member
    exact of_decide_eq_true (List.all_eq_true.mp bitsBelow column member)
  intro row member term present
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with boolean | rfl
  · obtain ⟨column,inside,rfl⟩ := List.mem_map.mp boolean
    simp only [booleanRow,List.mem_append,List.mem_singleton] at present
    rcases present with rfl | rfl <;> exact columns column inside
  · simp only [reconstructionRow,List.append_nil,List.mem_cons] at present
    rcases present with rfl | present
    · exact valueBelow
    · exact weighted_below upper _ 1 columns term present

set_option pp.all true in
#check @weighted_below
#print axioms weighted_below
set_option pp.all true in
#check @initial_rows_below
#print axioms initial_rows_below

end ShielddSecurity.ScalarBitFootprint
