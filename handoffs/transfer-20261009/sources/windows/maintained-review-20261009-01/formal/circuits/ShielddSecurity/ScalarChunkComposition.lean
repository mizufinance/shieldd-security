import ShielddSecurity.ScalarComparisonBounds
import ShielddSecurity.ScalarIndexed

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace ShielddSecurity.ScalarChunkComposition

/-- Exact row inclusion, rather than a digest or source-node name, transports
local dense certificates to one common relation read by the same rho. -/
theorem row_check_lift (p : Nat) (localRows commonRows : List Row)
    (included : ∀ row ∈ localRows, row ∈ commonRows) (expected : Row)
    (checked : Compiler.checkRow p localRows expected = true) :
    Compiler.checkRow p commonRows expected = true := by
  obtain ⟨actual, member, accepted⟩ := List.any_eq_true.mp checked
  exact List.any_eq_true.mpr ⟨actual, included actual member, accepted⟩

theorem product_check_lift (p : Nat) (localRows commonRows : List Row)
    (included : ∀ row ∈ localRows, row ∈ commonRows)
    (left right output : Linear) (data : ScalarRows.ProductData)
    (checked : ScalarRows.checkProduct p localRows left right output data = true) :
    ScalarRows.checkProduct p commonRows left right output data = true := by
  cases data with
  | foldedLeft coefficient => exact checked
  | foldedRight coefficient => exact checked
  | square =>
      simp only [ScalarRows.checkProduct, Bool.and_eq_true] at checked ⊢
      exact ⟨checked.1, row_check_lift p localRows commonRows included _ checked.2⟩
  | product auxiliary =>
      simp only [ScalarRows.checkProduct, Bool.and_eq_true] at checked ⊢
      exact ⟨row_check_lift p localRows commonRows included _ checked.1,
        row_check_lift p localRows commonRows included _ checked.2⟩

theorem step_check_lift (p : Nat) (localRows commonRows : List Row)
    (included : ∀ row ∈ localRows, row ∈ commonRows) (step : ScalarRows.StepData)
    (checked : ScalarRows.checkStep p localRows step = true) :
    ScalarRows.checkStep p commonRows step = true := by
  simp only [ScalarRows.checkStep, Bool.and_eq_true] at checked ⊢
  exact ⟨checked.1, product_check_lift p localRows commonRows included _ _ _ _ checked.2⟩

theorem chain_check_lift (p : Nat) (localRows commonRows : List Row)
    (included : ∀ row ∈ localRows, row ∈ commonRows)
    (initial : Linear) (steps : List ScalarRows.StepData)
    (checked : ScalarRows.checkChain p localRows initial steps = true) :
    ScalarRows.checkChain p commonRows initial steps = true := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step tail ih =>
      simp only [ScalarRows.checkChain, Bool.and_eq_true] at checked ⊢
      exact ⟨⟨checked.1.1, step_check_lift p localRows commonRows included step checked.1.2⟩,
        ih step.after checked.2⟩

theorem bits_check_lift (p : Nat) (localRows commonRows : List Row)
    (included : ∀ row ∈ localRows, row ∈ commonRows) (bits : List Linear)
    (checked : ScalarBits.checkBits p localRows bits = true) :
    ScalarBits.checkBits p commonRows bits = true := by
  apply List.all_eq_true.mpr
  intro bit member
  exact row_check_lift p localRows commonRows included ⟨bit, bit⟩
    (List.all_eq_true.mp checked bit member)

/-- Reuse bounded Boolean certificates in their original bit order. -/
theorem bits_append (p : Nat) (rows : List Row) (front back : List Linear)
    (first : ScalarBits.checkBits p rows front = true)
    (second : ScalarBits.checkBits p rows back = true) :
    ScalarBits.checkBits p rows (front ++ back) = true := by
  simpa only [ScalarBits.checkBits, List.all_append, Bool.and_eq_true] using
    And.intro first second

def checkBitChunks (p : Nat) (rows : List Row) : List (List Linear) → Bool
  | [] => true
  | chunk :: tail => ScalarBits.checkBits p rows chunk && checkBitChunks p rows tail

/-- Symbolic composition only; each concrete chunk still needs its own audit. -/
theorem bit_chunks_certificate (p : Nat) (rows : List Row) (chunks : List (List Linear))
    (checked : checkBitChunks p rows chunks = true) :
    ScalarBits.checkBits p rows chunks.flatten = true := by
  induction chunks with
  | nil => rfl
  | cons chunk tail ih =>
      simp only [checkBitChunks, Bool.and_eq_true] at checked
      exact bits_append p rows chunk tail.flatten checked.1 (ih checked.2)

theorem equality_check_lift (p : Nat) (localRows commonRows : List Row)
    (included : ∀ row ∈ localRows, row ∈ commonRows) (left right : Linear)
    (checked : ScalarComparisonBounds.checkEquality p localRows left right = true) :
    ScalarComparisonBounds.checkEquality p commonRows left right = true := by
  simp only [ScalarComparisonBounds.checkEquality, Bool.or_eq_true] at checked ⊢
  rcases checked with forward | backward
  · exact Or.inl (row_check_lift p localRows commonRows included _ forward)
  · exact Or.inr (row_check_lift p localRows commonRows included _ backward)

/-- The start of the next chunk is the actual endpoint of the previous one.
No independent seed, trusted comparison result, or multiplication equation is
introduced at a chunk boundary. -/
theorem chain_append (p : Nat) (rows : List Row) (initial : Linear)
    (front back : List ScalarRows.StepData)
    (first : ScalarRows.checkChain p rows initial front = true)
    (second : ScalarRows.checkChain p rows
      (ScalarComparisonBounds.endpoint initial front) back = true) :
    ScalarRows.checkChain p rows initial (front ++ back) = true := by
  induction front generalizing initial with
  | nil => exact second
  | cons step tail ih =>
      simp only [ScalarRows.checkChain, Bool.and_eq_true] at first
      simp only [List.cons_append, ScalarRows.checkChain, Bool.and_eq_true]
      exact ⟨⟨first.1.1, first.1.2⟩, ih step.after first.2 second⟩

def checkChunks (p : Nat) (rows : List Row) : Linear → List (List ScalarRows.StepData) → Bool
  | _, [] => true
  | initial, chunk :: tail => ScalarRows.checkChain p rows initial chunk &&
      checkChunks p rows (ScalarComparisonBounds.endpoint initial chunk) tail

/-- Consumes separately proved bounded chunk certificates symbolically.
The full data checker is never discharged here by a wide decide walk. -/
theorem chunks_certificate (p : Nat) (rows : List Row) (initial : Linear)
    (chunks : List (List ScalarRows.StepData))
    (checked : checkChunks p rows initial chunks = true) :
    ScalarRows.checkChain p rows initial chunks.flatten = true := by
  induction chunks generalizing initial with
  | nil => rfl
  | cons chunk tail ih =>
      simp only [checkChunks, Bool.and_eq_true] at checked
      exact chain_append p rows initial chunk tail.flatten checked.1
        (ih (ScalarComparisonBounds.endpoint initial chunk) checked.2)

theorem chunks_sound {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (initial : Linear) (chunks : List (List ScalarRows.StepData))
    (checked : checkChunks p rows initial chunks = true) :
    eval rho (ScalarComparisonBounds.endpoint initial chunks.flatten) =
      ScalarRows.polynomialChain rho (eval rho initial) chunks.flatten := by
  have recurrence := ScalarRows.checked_chain_sound rho one four rows satisfied initial chunks.flatten
    (chunks_certificate p rows initial chunks checked)
  rwa [ScalarComparisonBounds.endpoint_value] at recurrence

theorem polynomial_append {F : Type} [Field F] (rho : Nat → F)
    (value : F) (front back : List ScalarRows.StepData) :
    ScalarRows.polynomialChain rho value (front ++ back) =
      ScalarRows.polynomialChain rho (ScalarRows.polynomialChain rho value front) back := by
  induction front generalizing value with
  | nil => rfl
  | cons step tail ih =>
      simp only [List.cons_append, ScalarRows.polynomialChain]
      exact ih _

#print axioms row_check_lift
#print axioms product_check_lift
#print axioms step_check_lift
#print axioms chain_check_lift
#print axioms bits_check_lift
#print axioms bits_append
#print axioms bit_chunks_certificate
#print axioms equality_check_lift
#print axioms chain_append
#print axioms chunks_certificate
#print axioms chunks_sound
#print axioms polynomial_append

end ShielddSecurity.ScalarChunkComposition
