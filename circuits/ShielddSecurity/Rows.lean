import ShielddSecurity.Range

set_option maxHeartbeats 600000
namespace ShielddSecurity

abbrev Linear := List (Nat × Int)
structure Row where
  a : Linear
  b : Linear
  deriving DecidableEq, Repr

def eval {F : Type} [Field F] (rho : Nat → F) : Linear → F
  | [] => 0
  | (column, coefficient) :: terms => (coefficient : F) * rho column + eval rho terms

def Satisfies {F : Type} [Field F] (rho : Nat → F) (rows : List Row) : Prop :=
  ∀ row ∈ rows, Square (eval rho row.a) (eval rho row.b)

def booleanRow (column : Nat) : Row := ⟨[(column,1)], [(column,1)]⟩

def weighted : List Nat → Int → Linear
  | [], _ => []
  | column :: columns, weight => (column,weight) :: weighted columns (weight*2)

def reconstructionRow (value : Nat) (bits : List Nat) : Row :=
  ⟨(value,-1) :: weighted bits 1, []⟩

def equalityRow (left right : Nat) : Row := ⟨[(left,1), (right,-1)], []⟩

def sumReconstructionRow (first second : Nat) (bits : List Nat) : Row :=
  ⟨(first,-1) :: (second,-1) :: weighted bits 1, []⟩

def comparisonRow (limitBits candidateBits : List Nat) (borrow difference bound : Nat) : Row :=
  ⟨weighted limitBits 1 ++ weighted candidateBits (-1) ++
    [(borrow,(bound : Int)), (difference,-1)], []⟩

variable {F : Type} [Field F]

theorem eval_append (rho : Nat → F) (a b : Linear) : eval rho (a ++ b) = eval rho a + eval rho b := by
  induction a with
  | nil => simp [eval]
  | cons head tail ih => simp [eval, ih, add_assoc]

theorem satisfies_block (blocks : List (List Row)) (block : List Row)
    (present : block ∈ blocks) (rho : Nat → F) (satisfied : Satisfies rho blocks.flatten) :
    Satisfies rho block := by
  intro row member
  exact satisfied row (List.mem_flatten.mpr ⟨block, present, member⟩)

theorem equality_row_sound (rows : List Row) (left right : Nat) (rho : Nat → F)
    (present : equalityRow left right ∈ rows) (satisfied : Satisfies rho rows) :
    rho left = rho right := by
  have h := square_zero _ (satisfied _ present)
  apply sub_eq_zero.mp
  simpa [equalityRow, eval, sub_eq_add_neg] using h

theorem weighted_eval (rho : Nat → F) (columns : List Nat) (weight : Int) :
    eval rho (weighted columns weight) = (weight : F) * fieldBinary (columns.map rho) := by
  induction columns generalizing weight with
  | nil => simp [weighted, eval, fieldBinary]
  | cons column columns ih =>
      simp [weighted, eval, fieldBinary, ih]
      ring

theorem reconstruction_row_sound (rows : List Row) (value : Nat) (bits : List Nat)
    (present : reconstructionRow value bits ∈ rows) (rho : Nat → F)
    (satisfied : Satisfies rho rows) : fieldBinary (bits.map rho) = rho value := by
  have row := square_zero _ (satisfied _ present)
  apply sub_eq_zero.mp
  simpa [reconstructionRow, eval, weighted_eval, sub_eq_add_neg, add_comm] using row

theorem sum_reconstruction_sound (rows : List Row) (first second : Nat) (bits : List Nat)
    (present : sumReconstructionRow first second bits ∈ rows) (rho : Nat → F)
    (satisfied : Satisfies rho rows) : fieldBinary (bits.map rho) = rho first + rho second := by
  have row := square_zero _ (satisfied _ present)
  apply sub_eq_zero.mp
  calc
    _ = eval rho (sumReconstructionRow first second bits).a := by
      simp [sumReconstructionRow, eval, weighted_eval]
      ring
    _ = 0 := row

theorem comparison_row_sound (rows : List Row) (limitBits candidateBits : List Nat)
    (borrow difference bound : Nat)
    (present : comparisonRow limitBits candidateBits borrow difference bound ∈ rows)
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    fieldBinary (limitBits.map rho) - fieldBinary (candidateBits.map rho) =
      rho difference - rho borrow * (bound : F) := by
  apply sub_eq_zero.mp
  calc
    _ = eval rho (comparisonRow limitBits candidateBits borrow difference bound).a := by
      simp [comparisonRow, eval_append, weighted_eval, eval]
      ring
    _ = 0 := square_zero _ (satisfied _ present)

theorem comparison_row_complete (limitBits candidateBits : List Nat)
    (borrow difference bound : Nat) (rho : Nat → F)
    (equation : fieldBinary (limitBits.map rho) - fieldBinary (candidateBits.map rho) =
      rho difference - rho borrow * (bound : F)) :
    Square (eval rho (comparisonRow limitBits candidateBits borrow difference bound).a)
      (eval rho (comparisonRow limitBits candidateBits borrow difference bound).b) := by
  have zero : eval rho (comparisonRow limitBits candidateBits borrow difference bound).a = 0 := by
    calc
      _ = fieldBinary (limitBits.map rho) - fieldBinary (candidateBits.map rho) -
          (rho difference - rho borrow * (bound : F)) := by
        simp [comparisonRow, eval_append, weighted_eval, eval]
        ring
      _ = 0 := sub_eq_zero.mpr equation
  simp only [Square, zero, zero_mul]
  rfl

theorem rows_bits_sound (rows : List Row) (bits : List Nat)
    (booleans : bits.all (fun i => decide (booleanRow i ∈ rows)) = true)
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    ∀ x ∈ bits.map rho, Square x x := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨column, hc, rfl⟩
  have row := satisfied (booleanRow column) (of_decide_eq_true ((List.all_eq_true.mp booleans) column hc))
  simpa [booleanRow, eval] using row

/-- A kernel-checked inclusion certificate selects constraints from actual rows.
Additional rows may restrict completeness but cannot invalidate this implication. -/
theorem rows_range_sound (rows : List Row) (value : Nat) (bits : List Nat)
    (booleans : bits.all (fun i => decide (booleanRow i ∈ rows)) = true)
    (reconstruction : reconstructionRow value bits ∈ rows)
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    ∃ n : Nat, n < 2 ^ bits.length ∧ (n : F) = rho value := by
  have hbits := rows_bits_sound rows bits booleans rho satisfied
  have sum := reconstruction_row_sound rows value bits reconstruction rho satisfied
  simpa using range_sound (bits.map rho) (rho value) hbits sum

theorem range_block_complete (value : Nat) (bits : List Nat) (rho : Nat → F)
    (booleans : ∀ x ∈ bits.map rho, Square x x)
    (reconstruction : fieldBinary (bits.map rho) = rho value) :
    Satisfies rho (bits.map booleanRow ++ [reconstructionRow value bits]) := by
  intro row present
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at present
  rcases present with ⟨column, member, rfl⟩ | rfl
  · simpa [booleanRow, eval] using booleans _ (List.mem_map.mpr ⟨column,member,rfl⟩)
  · simp [reconstructionRow, eval, weighted_eval, reconstruction, Square]

theorem sum_block_complete (first second : Nat) (bits : List Nat) (rho : Nat → F)
    (booleans : ∀ x ∈ bits.map rho, Square x x)
    (reconstruction : fieldBinary (bits.map rho) = rho first + rho second) :
    Satisfies rho (bits.map booleanRow ++ [sumReconstructionRow first second bits]) := by
  intro row present
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at present
  rcases present with ⟨column, member, rfl⟩ | rfl
  · simpa [booleanRow, eval] using booleans _ (List.mem_map.mpr ⟨column,member,rfl⟩)
  · simp [sumReconstructionRow, eval, weighted_eval, reconstruction, Square] <;> ring

/-- Exact completeness for the emitted component, including its three linking rows.
The caller supplies a legal bit encoding and the declared input/constant copies. -/
theorem range_rows_complete (value commitment outline : Nat) (bits : List Nat)
    (rho : Nat → F)
    (booleans : ∀ column ∈ bits, Square (rho column) (rho column))
    (reconstruction : fieldBinary (bits.map rho) = rho value)
    (publicCopy : rho 1 = rho value)
    (committedCopy : rho 2 = rho commitment)
    (constantCopy : rho 0 = rho outline) :
    Satisfies rho (bits.map booleanRow ++
      [reconstructionRow value bits, equalityRow 1 value,
       equalityRow 2 commitment, equalityRow 0 outline]) := by
  intro row present
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at present
  rcases present with ⟨column, member, rfl⟩ | rfl | rfl | rfl | rfl
  · simpa [booleanRow, eval] using booleans column member
  · simp [reconstructionRow, eval, weighted_eval, reconstruction, Square]
  · simp [equalityRow, eval, publicCopy, Square]
  · simp [equalityRow, eval, committedCopy, Square]
  · simp [equalityRow, eval, constantCopy, Square]

/-- A legal bit vector and arbitrary commitment extend to all private columns. -/
def rangeAssignment (bits : List Bool) (commitment : F) (column : Nat) : F :=
  if column < 5 then
    if column = 0 then 1 else
    if column = 1 ∨ column = 3 then (binary bits : F) else commitment
  else if column = bits.length + 5 then 1
  else if bits[column - 5]?.getD false then 1 else 0

theorem rangeAssignment_bits (bits : List Bool) (commitment : F) :
    (List.range' 5 bits.length).map (rangeAssignment bits commitment) =
      bits.map (fun b => if b then (1 : F) else 0) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have bound : i < bits.length := by simpa using hj
    simp only [List.getElem_map, List.getElem_range', Nat.mul_one]
    have low : ¬ 5 + i < 5 := by omega
    have last : 5 + i ≠ bits.length + 5 := by omega
    have index : 5 + i - 5 = i := by omega
    simp [rangeAssignment, low, last, index, List.getElem?_eq_getElem bound]

theorem range_assignment_satisfies (bits : List Bool) (commitment : F) :
    Satisfies (rangeAssignment bits commitment)
      ((List.range' 5 bits.length).map booleanRow ++
       [reconstructionRow 3 (List.range' 5 bits.length), equalityRow 1 3,
        equalityRow 2 4, equalityRow 0 (bits.length + 5)]) := by
  apply range_rows_complete
  · intro column member
    have mapped : rangeAssignment bits commitment column ∈
        bits.map (fun b => if b then (1 : F) else 0) := by
      rw [← rangeAssignment_bits]
      exact List.mem_map.mpr ⟨column, member, rfl⟩
    exact (range_completeness (F := F) bits).1 _ mapped
  · rw [rangeAssignment_bits, binary_cast]
    simp [rangeAssignment]
  · simp [rangeAssignment]
  · simp [rangeAssignment]
  · simp [rangeAssignment, show ¬ bits.length + 5 < 5 by omega]

#print axioms rows_range_sound
#print axioms range_rows_complete
end ShielddSecurity
