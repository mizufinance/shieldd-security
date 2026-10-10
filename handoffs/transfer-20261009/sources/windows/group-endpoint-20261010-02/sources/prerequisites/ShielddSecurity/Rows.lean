import ShielddSecurity.Range

set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity

structure Row where
  a : Linear
  b : Linear
  deriving DecidableEq, Repr


def Satisfies {F : Type} [Field F] (rho : Nat → F) (rows : List Row) : Prop :=
  ∀ row ∈ rows, Square (eval rho row.a) (eval rho row.b)

def booleanRow (column : Nat) : Row := ⟨[(column,1)], [(column,1)]⟩

def weighted : List Nat → Int → Linear
  | [], _ => []
  | column :: columns, weight => (column,weight) :: weighted columns (weight*2)

def reconstructionRow (value : Nat) (bits : List Nat) : Row :=
  ⟨(value,-1) :: weighted bits 1, []⟩

def scaleLinear (factor : Int) (terms : Linear) : Linear :=
  terms.map (fun (column, coefficient) => (column, factor * coefficient))

/-- A source expression may be fused into several columns. Its range proof must
use that exact expression, not invent a witness-column name for it. -/
def expressionReconstructionRow (value : Linear) (bits : List Nat) : Row :=
  ⟨weighted bits 1 ++ scaleLinear (-1) value, []⟩

def equalityRow (left right : Nat) : Row := ⟨[(left,1), (right,-1)], []⟩

def sumReconstructionRow (first second : Nat) (bits : List Nat) : Row :=
  ⟨(first,-1) :: (second,-1) :: weighted bits 1, []⟩

def comparisonRow (limitBits candidateBits : List Nat) (borrow difference bound : Nat) : Row :=
  ⟨weighted limitBits 1 ++ weighted candidateBits (-1) ++
    [(borrow,(bound : Int)), (difference,-1)], []⟩

variable {F : Type} [Field F]

/-- Local gadget completion may assign only its explicitly owned auxiliaries.
Everything else, including shared hash outputs and public inputs, is preserved. -/
def patchAssignment (base values : Nat → F) (fresh : List Nat) (column : Nat) : F :=
  if column ∈ fresh then values column else base column

omit [Field F] in
theorem patchAssignment_preserves (base values : Nat → F) (fresh : List Nat)
    (column : Nat) (outside : column ∉ fresh) :
    patchAssignment base values fresh column = base column := by
  simp [patchAssignment, outside]

theorem eval_agrees (left right : Nat → F) (terms : Linear)
    (agree : ∀ term ∈ terms, left term.1 = right term.1) :
    eval left terms = eval right terms := by
  revert agree
  induction terms with
  | nil => intro _; rfl
  | cons head tail ih =>
      intro agree
      rw [eval, eval, agree head (by simp)]
      rw [ih (by intro term member; exact agree term (by simp [member]))]

/-- An extension cannot break surrounding constraints whose actual supports
exclude the freshly assigned columns. This is a syntactic ownership condition,
not an assumption that unrelated hash/Merkle witnesses can be constructed. -/
theorem patch_preserves_rows (base values : Nat → F) (fresh : List Nat)
    (rows : List Row) (satisfied : Satisfies base rows)
    (disjoint : ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ fresh) :
    Satisfies (patchAssignment base values fresh) rows := by
  intro row member
  have left : eval (patchAssignment base values fresh) row.a = eval base row.a := by
    apply eval_agrees
    intro term present
    exact patchAssignment_preserves base values fresh term.1
      (disjoint row member term (List.mem_append.mpr (Or.inl present)))
  have right : eval (patchAssignment base values fresh) row.b = eval base row.b := by
    apply eval_agrees
    intro term present
    exact patchAssignment_preserves base values fresh term.1
      (disjoint row member term (List.mem_append.mpr (Or.inr present)))
  rw [left, right]
  exact satisfied row member

/-- Finite support certificates allow a generated gadget instance to discharge
the ownership condition in the kernel rather than trusting a Python set check. -/
theorem patch_preserves_rows_checked (base values : Nat → F) (fresh : List Nat)
    (rows : List Row) (satisfied : Satisfies base rows)
    (certificate : rows.all (fun row =>
      (row.a ++ row.b).all (fun term => decide (term.1 ∉ fresh))) = true) :
    Satisfies (patchAssignment base values fresh) rows := by
  apply patch_preserves_rows base values fresh rows satisfied
  intro row member term present
  exact of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp certificate) row member)) term present)

theorem eval_append (rho : Nat → F) (a b : Linear) : eval rho (a ++ b) = eval rho a + eval rho b := by
  induction a with
  | nil => simp [eval]
  | cons head tail ih => simp [eval, ih, add_assoc]

theorem eval_scale (rho : Nat → F) (terms : Linear) (factor : Int) :
    eval rho (scaleLinear factor terms) = (factor : F) * eval rho terms := by
  induction terms with
  | nil => simp [scaleLinear, eval]
  | cons head tail ih =>
      rcases head with ⟨column, coefficient⟩
      change (((factor * coefficient : Int) : F) * rho column +
        eval rho (scaleLinear factor tail)) =
        (factor : F) * ((coefficient : F) * rho column + eval rho tail)
      rw [ih, Int.cast_mul]
      ring

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

/-- All-assignment range soundness for an actually observed linear expression.
The membership certificate must include its complete compiled reconstruction. -/
theorem rows_expression_range_sound (rows : List Row) (value : Linear) (bits : List Nat)
    (booleans : bits.all (fun i => decide (booleanRow i ∈ rows)) = true)
    (reconstruction : expressionReconstructionRow value bits ∈ rows)
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    ∃ n : Nat, n < 2 ^ bits.length ∧ (n : F) = eval rho value := by
  have hbits := rows_bits_sound rows bits booleans rho satisfied
  have zero := square_zero _ (satisfied _ reconstruction)
  have equation : fieldBinary (bits.map rho) = eval rho value := by
    apply sub_eq_zero.mp
    simpa [expressionReconstructionRow, eval_append, weighted_eval, eval_scale,
      eval, sub_eq_add_neg] using zero
  simpa using range_sound (bits.map rho) (eval rho value) hbits equation

/-- This is satisfaction of the range block only; constructing assignments for
shared expressions and all other compiler rows is a separate extension proof. -/
theorem expression_range_block_complete (value : Linear) (bits : List Nat) (rho : Nat → F)
    (booleans : ∀ x ∈ bits.map rho, Square x x)
    (reconstruction : fieldBinary (bits.map rho) = eval rho value) :
    Satisfies rho (bits.map booleanRow ++ [expressionReconstructionRow value bits]) := by
  intro row present
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at present
  rcases present with ⟨column, member, rfl⟩ | rfl
  · simpa [booleanRow, eval] using booleans _ (List.mem_map.mpr ⟨column,member,rfl⟩)
  · simp [expressionReconstructionRow, eval_append, weighted_eval, eval_scale,
      eval, reconstruction, Square]

theorem range_block_complete (value : Nat) (bits : List Nat) (rho : Nat → F)
    (booleans : ∀ x ∈ bits.map rho, Square x x)
    (reconstruction : fieldBinary (bits.map rho) = rho value) :
    Satisfies rho (bits.map booleanRow ++ [reconstructionRow value bits]) := by
  intro row present
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at present
  rcases present with ⟨column, member, rfl⟩ | rfl
  · simpa [booleanRow, eval] using booleans _ (List.mem_map.mpr ⟨column,member,rfl⟩)
  · simp [reconstructionRow, eval, weighted_eval, reconstruction, Square]

/-- Assign only a contiguous private bit block; retain the entire surrounding
assignment. Callers must check that this block is fresh for their other rows. -/
def writeBits (base : Nat → F) (start : Nat) (bits : List Bool) (column : Nat) : F :=
  if start ≤ column ∧ column < start + bits.length then
    if bits[column - start]?.getD false then 1 else 0
  else base column

theorem writeBits_preserves (base : Nat → F) (start : Nat) (bits : List Bool)
    (column : Nat) (outside : column < start ∨ start + bits.length ≤ column) :
    writeBits base start bits column = base column := by
  have no : ¬ (start ≤ column ∧ column < start + bits.length) := by omega
  simp [writeBits, no]

theorem writeBits_map (base : Nat → F) (start : Nat) (bits : List Bool) :
    (List.range' start bits.length).map (writeBits base start bits) =
      bits.map (fun b => if b then (1 : F) else 0) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have bound : i < bits.length := by simpa using hj
    simp only [List.getElem_map, List.getElem_range']
    have lower : start ≤ start + i := by omega
    have upper : start + i < start + bits.length := by omega
    have index : start + i - start = i := by omega
    simp [writeBits, lower, upper, index, List.getElem?_eq_getElem bound]

/-- Constructive range completion preserving the value and every other column.
This is suitable before building hash/Merkle gadgets which consume these bits;
it does not assert that existing rows which read the bit block are preserved. -/
theorem writeBits_range_complete (base : Nat → F) (value start width n : Nat)
    (bound : n < 2^width) (meaning : base value = (n : F))
    (outside : value < start ∨ start + width ≤ value) :
    Satisfies (writeBits base start (encodeBits width n))
      ((List.range' start width).map booleanRow ++
        [reconstructionRow value (List.range' start width)]) := by
  have mapped : (List.range' start width).map (writeBits base start (encodeBits width n)) =
      (encodeBits width n).map (fun b => if b then (1 : F) else 0) := by
    simpa using writeBits_map base start (encodeBits width n)
  apply range_block_complete
  · rw [mapped]
    exact (range_completeness (F := F) (encodeBits width n)).1
  · rw [mapped, binary_cast, encodeBits_value width n bound]
    rw [writeBits_preserves base start (encodeBits width n) value (by simpa using outside)]
    exact meaning.symm

theorem sum_block_complete (first second : Nat) (bits : List Nat) (rho : Nat → F)
    (booleans : ∀ x ∈ bits.map rho, Square x x)
    (reconstruction : fieldBinary (bits.map rho) = rho first + rho second) :
    Satisfies rho (bits.map booleanRow ++ [sumReconstructionRow first second bits]) := by
  intro row present
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at present
  rcases present with ⟨column, member, rfl⟩ | rfl
  · simpa [booleanRow, eval] using booleans _ (List.mem_map.mpr ⟨column,member,rfl⟩)
  · simp [sumReconstructionRow, eval, weighted_eval, reconstruction, Square]

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
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at present
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
    simp only [List.getElem_map, List.getElem_range']
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

end ShielddSecurity

-- Fresh handwritten bounded successor; proof bodies retained.
set_option pp.all true in
#check @ShielddSecurity.rows_range_sound
#print axioms ShielddSecurity.rows_range_sound
set_option pp.all true in
#check @ShielddSecurity.rows_expression_range_sound
#print axioms ShielddSecurity.rows_expression_range_sound
set_option pp.all true in
#check @ShielddSecurity.expression_range_block_complete
#print axioms ShielddSecurity.expression_range_block_complete
set_option pp.all true in
#check @ShielddSecurity.range_rows_complete
#print axioms ShielddSecurity.range_rows_complete
set_option pp.all true in
#check @ShielddSecurity.patch_preserves_rows
#print axioms ShielddSecurity.patch_preserves_rows
set_option pp.all true in
#check @ShielddSecurity.writeBits_range_complete
#print axioms ShielddSecurity.writeBits_range_complete
