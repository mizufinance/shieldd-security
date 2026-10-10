import ShielddSecurity.MerkleSelection26Proof
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleSelection26Semantic
open Compiler CompilerCompletion CompilerIndexed01 CompilerSegmentCompletion11
open CapturedInitial73419Generic01 (p copy normalized)
namespace D
abbrev rows := MerkleSelection26Data.originalRows
abbrev left := MerkleSelection26Data.left
abbrev right := MerkleSelection26Data.right
abbrev outputs := MerkleSelection26Data.outputs
end D
def leaf := RegistryWhole23.actualResult
def pivot (i : Fin 6) : Linear := [(25460+2*i.val,1)]
def auxiliary (i : Fin 6) : Linear := [(25461+2*i.val,1)]
def selector (i : Fin 6) : Nat := if i.val<2 then 184 else 185
def rightSpec (i : Fin 6) : Linear :=
  if i.val=0 then subtract [(136,1)] leaf else
  if i.val=1 then subtract [(138,1)] leaf else
  if i.val=2 then subtract [(136,1)] (leaf++[(25460,1)]) else
  if i.val=3 then subtract [(137,1)] (subtract [(136,1)] [(25460,1)]) else
  if i.val=4 then subtract (leaf++[(25462,1)]) [(137,1)] else [(25462,-1)]
def outputSpec (i : Fin 4) : Linear :=
  if i.val=0 then leaf++[(25460,1),(25464,1)] else
  if i.val=1 then [(136,1),(25460,-1),(25466,1)] else
  if i.val=2 then [(137,1),(25468,1)] else [(138,1),(25470,1)]
theorem inputs_checked : (List.finRange 6).all (fun i => decide
    (canonical p (D.left i)=canonical p [(selector i,1)] ∧ canonical p (D.right i)=canonical p (rightSpec i)))=true := by decide +kernel
theorem products_checked : (List.finRange 6).all (fun i =>
    checkRow p (normalized D.rows) ⟨subtract (D.left i) (D.right i),auxiliary i⟩ &&
    checkRow p (normalized D.rows) ⟨D.left i++D.right i,auxiliary i++scaleLinear 4 (pivot i)⟩)=true := by decide +kernel
theorem outputs_checked : (List.finRange 4).all (fun i => decide
    (canonical p (D.outputs i)=canonical p (outputSpec i)))=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem values (rho : Nat → F) (linked : rho copy=rho 0) (sat : Satisfies rho D.rows) (i : Fin 6) :
    rho (25460+2*i.val)=rho (selector i)*eval rho (rightSpec i) := by
  have checks := List.all_eq_true.mp products_checked i (List.mem_finRange i)
  have bindings := of_decide_eq_true (List.all_eq_true.mp inputs_checked i (List.mem_finRange i))
  have source := CapturedInitial73419Generic01.normalized_satisfied D.rows rho linked sat
  have value := checked_product_sound rho (normalized D.rows) (D.left i) (D.right i) (pivot i) (auxiliary i)
    CapturedRegistryLeaf20R0Proof01.four_ne_zero source (Bool.and_eq_true_iff.mp checks).1 (Bool.and_eq_true_iff.mp checks).2
  rw [canonical_equal rho _ _ bindings.1,canonical_equal rho _ _ bindings.2] at value
  simpa [pivot,eval] using value
omit [CharP F p] in
def formula (low high node sibling0 sibling1 sibling2 : F) (i : Fin 4) : F :=
  let leftFirst := node+low*(sibling0-node)
  let leftSecond := sibling0-low*(sibling0-node)
  let rightThird := node+low*(sibling2-node)
  let rightFourth := sibling2-low*(sibling2-node)
  if i.val=0 then leftFirst+high*(sibling0-leftFirst) else
  if i.val=1 then leftSecond+high*(sibling1-leftSecond) else
  if i.val=2 then sibling1+high*(rightThird-sibling1) else sibling2+high*(rightFourth-sibling2)
theorem arbitrary (rho : Nat → F) (linked : rho copy=rho 0) (sat : Satisfies rho D.rows) :
    (fun i => eval rho (D.outputs i))=formula (rho 184) (rho 185) (eval rho leaf) (rho 136) (rho 137) (rho 138) := by
  have v0 := values rho linked sat (⟨0,by decide⟩ : Fin 6)
  have v1 := values rho linked sat (⟨1,by decide⟩ : Fin 6)
  have v2 := values rho linked sat (⟨2,by decide⟩ : Fin 6)
  have v3 := values rho linked sat (⟨3,by decide⟩ : Fin 6)
  have v4 := values rho linked sat (⟨4,by decide⟩ : Fin 6)
  have v5 := values rho linked sat (⟨5,by decide⟩ : Fin 6)
  simp [selector,rightSpec,eval_subtract,eval_append,eval] at v0 v1 v2 v3 v4 v5
  funext i
  have binding := of_decide_eq_true (List.all_eq_true.mp outputs_checked i (List.mem_finRange i))
  rw [canonical_equal rho _ _ binding]
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl
  · change eval rho (leaf++[(25460,1),(25464,1)]) = eval rho leaf+rho 184*(rho 136-eval rho leaf)+rho 185*(rho 136-(eval rho leaf+rho 184*(rho 136-eval rho leaf)))
    rw [eval_append]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [v2,v0]
    ring
  · change eval rho [(136,1),(25460,-1),(25466,1)] = rho 136-rho 184*(rho 136-eval rho leaf)+rho 185*(rho 137-(rho 136-rho 184*(rho 136-eval rho leaf)))
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero]
    rw [v3,v0]
    ring
  · change eval rho [(137,1),(25468,1)] = rho 137+rho 185*(eval rho leaf+rho 184*(rho 138-eval rho leaf)-rho 137)
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [v4,v1]
  · change eval rho [(138,1),(25470,1)] = rho 138+rho 185*((rho 138-rho 184*(rho 138-eval rho leaf))-rho 138)
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [v5,v1]
    ring

def completed (base : Nat → F) : Nat → F := run base MerkleSelection26Data.steps
include F in
theorem prior_support (row : Row)
    (member : row∈CapturedPriorRows16Frame01.capturedPriorRows++TransferPoseidonThreeCallJoin15Program01.originalRows++RegistryWhole23.selectedRows)
    (term : Nat×Int) (present : term∈row.a++row.b) : term.1<25460 ∨ 25472≤term.1 := by
  rcases List.mem_append.mp member with member|member
  · rcases List.mem_append.mp member with member|member
    · have bound := CapturedPriorRows16Frame01.columns_below row member term present
      exact Or.inl (by omega)
    · rcases List.mem_append.mp member with member|member
      · rcases (TransferPoseidonThreeCallJoin15Frame01.whole_segment (F:=F)).support row member term present with below|equal
        · exact Or.inl (by change term.1<25044 at below;omega)
        · exact Or.inr (by change term.1=200692 at equal;omega)
      · have checked : CapturedInitial73419Generic01.supportCheck 25044 [TransferPoseidonWidth3Call08Shared01.rawCopy]=true := by decide +kernel
        have bound := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
        rcases bound with below|equal
        · exact Or.inl (by omega)
        · exact Or.inr (by change term.1=200692 at equal;omega)
  · have found := (RegistryWhole23.membership row).mpr member
    rcases (RegistryWhole23.segment (F:=F)).support row found term present with below|equal
    · exact Or.inl below
    · exact Or.inr (by change term.1=200692 at equal;omega)
def final (base : Nat → F) := completed (RegistryWhole23.final base)
theorem final_rows (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (final base) CapturedPriorRows16Frame01.capturedPriorRows ∧
    Satisfies (final base) TransferPoseidonThreeCallJoin15Program01.originalRows ∧
    Satisfies (final base) RegistryWhole23.selectedRows ∧ Satisfies (final base) D.rows := by
  have old := RegistryWhole23.same_assignment_rows base linked
  have combined : Satisfies (RegistryWhole23.final base)
      (CapturedPriorRows16Frame01.capturedPriorRows++TransferPoseidonThreeCallJoin15Program01.originalRows++RegistryWhole23.selectedRows) := by
    intro row member
    rcases List.mem_append.mp member with member|member
    · rcases List.mem_append.mp member with member|member
      · exact old.1 row member
      · exact old.2.1 row member
    · exact old.2.2 row member
  have preserved := CompilerSegmentCompletion11.prior_preserved copy (MerkleSelection26Proof.segment (F:=F)) _ _ combined (prior_support (F:=F))
  refine ⟨?_,?_,?_,?_⟩
  · exact fun row member => preserved row (List.mem_append_left _ (List.mem_append_left _ member))
  · exact fun row member => preserved row (List.mem_append_left _ (List.mem_append_right _ member))
  · exact fun row member => preserved row (List.mem_append_right _ member)
  · apply MerkleSelection26Proof.completed
    rw [RegistryWhole23.final_outside base copy (Or.inr (by decide)),RegistryWhole23.final_outside base 0 (Or.inl (by decide))]
    exact linked
end ShielddSecurity.MerkleSelection26Semantic

set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.D.rows
#print axioms ShielddSecurity.MerkleSelection26Semantic.D.rows
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.D.left
#print axioms ShielddSecurity.MerkleSelection26Semantic.D.left
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.D.right
#print axioms ShielddSecurity.MerkleSelection26Semantic.D.right
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.D.outputs
#print axioms ShielddSecurity.MerkleSelection26Semantic.D.outputs
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.leaf
#print axioms ShielddSecurity.MerkleSelection26Semantic.leaf
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.pivot
#print axioms ShielddSecurity.MerkleSelection26Semantic.pivot
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.auxiliary
#print axioms ShielddSecurity.MerkleSelection26Semantic.auxiliary
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.selector
#print axioms ShielddSecurity.MerkleSelection26Semantic.selector
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.rightSpec
#print axioms ShielddSecurity.MerkleSelection26Semantic.rightSpec
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.outputSpec
#print axioms ShielddSecurity.MerkleSelection26Semantic.outputSpec
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.inputs_checked
#print axioms ShielddSecurity.MerkleSelection26Semantic.inputs_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.products_checked
#print axioms ShielddSecurity.MerkleSelection26Semantic.products_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.outputs_checked
#print axioms ShielddSecurity.MerkleSelection26Semantic.outputs_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.values
#print axioms ShielddSecurity.MerkleSelection26Semantic.values
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.formula
#print axioms ShielddSecurity.MerkleSelection26Semantic.formula
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.arbitrary
#print axioms ShielddSecurity.MerkleSelection26Semantic.arbitrary
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.completed
#print axioms ShielddSecurity.MerkleSelection26Semantic.completed
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.prior_support
#print axioms ShielddSecurity.MerkleSelection26Semantic.prior_support
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.final
#print axioms ShielddSecurity.MerkleSelection26Semantic.final
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Semantic.final_rows
#print axioms ShielddSecurity.MerkleSelection26Semantic.final_rows
