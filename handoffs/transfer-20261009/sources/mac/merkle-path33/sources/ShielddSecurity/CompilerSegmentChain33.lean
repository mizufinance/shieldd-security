import ShielddSecurity.CompilerSegmentCompletion11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerSegmentChain33
open Compiler CompilerCompletion CompilerSegmentCompletion11
variable {F : Type} [Field F]
def steps (copy : Nat) (piece : Nat → Segment F copy) : Nat → List Step
  | 0 => []
  | n+1 => steps copy piece n ++ (piece n).steps
def rows (copy : Nat) (piece : Nat → Segment F copy) : Nat → List Row
  | 0 => []
  | n+1 => rows copy piece n ++ (piece n).rows
structure Bounds (copy start stride count : Nat) (piece : Nat → Segment F copy) : Prop where
  low : ∀ i<count,(piece i).low=start+stride*i
  high : ∀ i<count,(piece i).high=start+stride*(i+1)
  start_pos : 0<start
  copy_above : start+stride*count≤copy

theorem writes_bound (copy start stride count : Nat) (piece : Nat → Segment F copy)
    (bounds : Bounds copy start stride count piece) (n : Nat) (hn : n≤count) :
    ∀ column∈PoseidonCompletion.writes (steps copy piece n),start≤column ∧ column<start+stride*n := by
  induction n with
  | zero => simp [steps,PoseidonCompletion.writes]
  | succ n ih =>
    intro column member
    simp only [steps,PoseidonCompletion.writes,List.flatMap_append,List.mem_append] at member
    rcases member with member|member
    · have b := ih (by omega) column member
      constructor
      · exact b.1
      · have h : stride*n≤stride*(n+1) := Nat.mul_le_mul_left stride (by omega)
        omega
    · have b := (piece n).writes column member
      rw [bounds.low n (by omega),bounds.high n (by omega)] at b
      constructor
      · omega
      · exact b.2

theorem support_bound (copy start stride count : Nat) (piece : Nat → Segment F copy)
    (bounds : Bounds copy start stride count piece) (n : Nat) (hn : n≤count) :
    ∀ row∈rows copy piece n,∀ term∈row.a++row.b,term.1<start+stride*n ∨ term.1=copy := by
  induction n with
  | zero => simp [rows]
  | succ n ih =>
    intro row member term present
    rcases List.mem_append.mp member with member|member
    · rcases ih (by omega) row member term present with b|e
      · have h : stride*n≤stride*(n+1) := Nat.mul_le_mul_left stride (by omega)
        exact Or.inl (by omega)
      · exact Or.inr e
    · have b := (piece n).support row member term present
      rw [bounds.high n (by omega)] at b
      exact b

theorem complete (copy start stride count : Nat) (piece : Nat → Segment F copy)
    (bounds : Bounds copy start stride count piece) (n : Nat) (hn : n≤count)
    (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (run base (steps copy piece n)) (rows copy piece n) := by
  induction n with
  | zero => intro row member;cases member
  | succ n ih =>
    have previous := ih (by omega)
    have endpoint : start+stride*n≤copy := by
      have m := Nat.mul_le_mul_left stride (show n≤count by omega)
      have c := bounds.copy_above
      omega
    have copyFrame : run base (steps copy piece n) copy=base copy := by
      apply PoseidonCompletion.run_outside
      intro member
      have b := writes_bound copy start stride count piece bounds n (by omega) copy member
      omega
    have zeroFrame : run base (steps copy piece n) 0=base 0 := by
      apply PoseidonCompletion.run_outside
      intro member
      have b := writes_bound copy start stride count piece bounds n (by omega) 0 member
      have positive := bounds.start_pos
      omega
    have next := (piece n).complete (run base (steps copy piece n)) (by rw [copyFrame,zeroFrame];exact linked)
    have preserved := CompilerSequenceCompletion.preserves_rows (run base (steps copy piece n)) (piece n).steps
      (rows copy piece n) previous (by
        intro row member term present written
        have support := support_bound copy start stride count piece bounds n (by omega) row member term present
        have write := (piece n).writes term.1 written
        rw [bounds.low n (by omega),bounds.high n (by omega)] at write
        have upper : start+stride*(n+1)≤copy := by
          have m := Nat.mul_le_mul_left stride (show n+1≤count by omega)
          have c := bounds.copy_above
          omega
        rcases support with below|equal
        · omega
        · omega)
    rw [steps,CompilerSequenceCompletion.run_append]
    intro row member
    rcases List.mem_append.mp member with member|member
    · exact preserved row member
    · exact next row member

def segment (copy start stride count : Nat) (piece : Nat → Segment F copy)
    (bounds : Bounds copy start stride count piece) (n : Nat) (hn : n≤count) : Segment F copy where
  steps := steps copy piece n
  rows := rows copy piece n
  low := start
  high := start+stride*n
  writes := writes_bound copy start stride count piece bounds n hn
  support := support_bound copy start stride count piece bounds n hn
  complete := complete copy start stride count piece bounds n hn
theorem rows_member (copy : Nat) (piece : Nat → Segment F copy) (n i : Nat) (less : i<n)
    (row : Row) (member : row∈(piece i).rows) : row∈rows copy piece n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases equal : i=n
    · subst i
      exact List.mem_append_right _ member
    · exact List.mem_append_left _ (ih (by omega))
end ShielddSecurity.CompilerSegmentChain33

set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.steps
#print axioms ShielddSecurity.CompilerSegmentChain33.steps
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.rows
#print axioms ShielddSecurity.CompilerSegmentChain33.rows
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.Bounds
#print axioms ShielddSecurity.CompilerSegmentChain33.Bounds
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.writes_bound
#print axioms ShielddSecurity.CompilerSegmentChain33.writes_bound
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.support_bound
#print axioms ShielddSecurity.CompilerSegmentChain33.support_bound
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.complete
#print axioms ShielddSecurity.CompilerSegmentChain33.complete
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.segment
#print axioms ShielddSecurity.CompilerSegmentChain33.segment
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentChain33.rows_member
#print axioms ShielddSecurity.CompilerSegmentChain33.rows_member
