import ShielddSecurity.MerkleFamily32Whole
import ShielddSecurity.CompilerSegmentChain33
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerklePath33
open Compiler CompilerCompletion CompilerSegmentCompletion11
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
def piece (n : Nat) : Segment F copy := MerkleFamily32Whole.segment ⟨n%15,Nat.mod_lt n (by decide)⟩
theorem bounds : CompilerSegmentChain33.Bounds copy 25884 424 15 (piece (F:=F)) where
  low := by
    intro n hn
    change (MerkleFamily32Whole.segment (F:=F) ⟨n%15,Nat.mod_lt n (by decide)⟩).low=_
    have equal : (⟨n%15,Nat.mod_lt n (by decide)⟩ : Fin 15)=⟨n,hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
    rw [equal]
    exact (MerkleFamily32Whole.bounds ⟨n,hn⟩).1
  high := by
    intro n hn
    change (MerkleFamily32Whole.segment (F:=F) ⟨n%15,Nat.mod_lt n (by decide)⟩).high=_
    have equal : (⟨n%15,Nat.mod_lt n (by decide)⟩ : Fin 15)=⟨n,hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
    rw [equal]
    have result := (MerkleFamily32Whole.bounds (F:=F) ⟨n,hn⟩).2
    change (MerkleFamily32Whole.segment (F:=F) ⟨n,hn⟩).high=25884+424*(n+1)
    rw [result]
    change 26308+424*n=25884+424*(n+1)
    omega
  start_pos := by decide
  copy_above := by decide
def segment : Segment F copy := CompilerSegmentChain33.segment copy 25884 424 15 (piece (F:=F)) bounds 15 (by decide)
def rows := (segment (F:=F)).rows
def completed (base : Nat → F) := run base (segment (F:=F)).steps
theorem complete (base : Nat → F) (linked : base copy=base 0) : Satisfies (completed base) (rows (F:=F)) :=
  (segment (F:=F)).complete base linked
theorem outside (base : Nat → F) (column : Nat) (bound : column<25884 ∨ 32244≤column) : completed base column=base column :=
  CompilerSegmentCompletion11.outside copy (segment (F:=F)) base column bound
omit [CharP F p] in
def observed (rho : Nat → F) (n : Nat) : F :=
  if n=0 then eval rho MerkleHash27Whole.actualResult else eval rho (MerkleFamily32Tables.resultList[n-1]?.getD [])
omit [CharP F p] in
def path (rho : Nat → F) : Nat → F
  | 0 => eval rho MerkleHash27Whole.actualResult
  | n+1 => MerkleFamily32Whole.next ⟨n%15,Nat.mod_lt n (by decide)⟩ rho (path rho n)
omit [CharP F p] in
theorem previous_eq (i : Fin 15) (rho : Nat → F) : eval rho (MerkleFamily32Tables.previousResult i)=observed rho i.val := by
  unfold MerkleFamily32Tables.previousResult observed
  split_ifs <;> rfl
omit [CharP F p] in
theorem observed_succ (n : Nat) (hn : n<15) (rho : Nat → F) : observed rho (n+1)=eval rho (MerkleFamily32Tables.actualResult ⟨n,hn⟩) := by
  simp only [observed,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,MerkleFamily32Tables.actualResult]
theorem all_level_rows (rho : Nat → F) (sat : Satisfies rho (rows (F:=F))) (i : Fin 15) :
    Satisfies rho (MerkleFamily32Whole.rows (F:=F) i) := by
  intro row member
  apply sat row
  apply CompilerSegmentChain33.rows_member copy (piece (F:=F)) 15 i.val i.isLt row
  change row∈(MerkleFamily32Whole.segment (F:=F) ⟨i.val%15,Nat.mod_lt i.val (by decide)⟩).rows
  have equal : (⟨i.val%15,Nat.mod_lt i.val (by decide)⟩ : Fin 15)=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [equal]
  exact member
theorem arbitrary_path (rho : Nat → F) (one : rho 0=1) (sat : Satisfies rho (rows (F:=F)))
    (n : Nat) (hn : n≤15) : observed rho n=path rho n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have bound : n<15 := by omega
    have step := MerkleFamily32Whole.arbitrary_step ⟨n,bound⟩ rho one (all_level_rows rho sat ⟨n,bound⟩)
    rw [previous_eq,ih (by omega)] at step
    rw [observed_succ n bound]
    simpa only [path,Nat.mod_eq_of_lt bound] using step
end ShielddSecurity.MerklePath33
