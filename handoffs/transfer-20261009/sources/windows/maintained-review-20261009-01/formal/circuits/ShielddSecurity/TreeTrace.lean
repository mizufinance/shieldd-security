import ShielddSecurity.TreeBinding

set_option maxHeartbeats 200000

namespace ShielddSecurity.TreeTrace

variable {F : Type} [Field F]

/-- Deterministic bit choice for a constrained field bit. It is used only after
an actual-row theorem proves the field value is one of zero/one. -/
noncomputable def bitOf (value : F) : Bool := by
  classical
  exact if value = 0 then false else true

theorem bitOf_of_bit (value : Bool) : bitOf (Tree.bit value : F) = value := by
  cases value <;> simp [bitOf, Tree.bit]

/-- Symbolic path concatenation; no constraint walk or hash injectivity. -/
theorem root_append (hash : Nat → List F → F) (level : Nat) (node : F)
    (left right : List (TreeBinding.Step F)) :
    TreeBinding.root hash level node (left ++ right) =
      TreeBinding.root hash (level + left.length) (TreeBinding.root hash level node left) right := by
  induction left generalizing level node with
  | nil => simp [TreeBinding.root]
  | cons step tail ih =>
      simp only [List.cons_append,TreeBinding.root,List.length_cons]
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (level + 1) (hash level
          (Tree.children step.low step.high node step.first step.second step.third))

/-- The generated instance supplies each local transition from its imported
actual ordered-child and complete hash theorems. A desired final root is never
a premise. Position/range and native byte interpretation remain separate joins. -/
theorem sequence_root (hash : Nat → List F → F) (start count : Nat)
    (nodes : Nat → F) (steps : Nat → TreeBinding.Step F)
    (transitions : ∀ index, index < count → nodes (index + 1) =
      hash (start + index) (Tree.children (steps index).low (steps index).high (nodes index)
        (steps index).first (steps index).second (steps index).third)) :
    TreeBinding.root hash start (nodes 0) ((List.range count).map steps) = nodes count := by
  revert transitions
  induction count with
  | zero => intro _; simp [TreeBinding.root]
  | succ count ih =>
      intro transitions
      rw [List.range_succ,List.map_append,root_append]
      rw [ih (fun index bound => transitions index (Nat.lt_succ_of_lt bound))]
      simp only [List.length_map,List.length_range,List.map_cons,List.map_nil,TreeBinding.root]
      exact (transitions count (Nat.lt_succ_self count)).symm

set_option pp.all true in
#check @bitOf_of_bit
#print axioms bitOf_of_bit
set_option pp.all true in
#check @root_append
#print axioms root_append
set_option pp.all true in
#check @sequence_root
#print axioms sequence_root

end ShielddSecurity.TreeTrace
