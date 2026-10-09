import ShielddSecurity.CompilerRecipe01
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.CompilerRecipeTree01
open Compiler CompilerRecipe01
inductive Tree where
  | leaf (record : Record)
  | branch (leftSize : Nat) (left right : Tree)
  deriving DecidableEq

def Tree.size : Tree → Nat
  | .leaf _ => 1
  | .branch count _ right => count+right.size

def Tree.toList : Tree → List Record
  | .leaf record => [record]
  | .branch _ left right => left.toList++right.toList

def Tree.check : Tree → Bool
  | .leaf _ => true
  | .branch count left right => decide (count=left.size) && left.check && right.check

def Tree.lookup : Tree → Nat → Option Record
  | .leaf record,index => if index=0 then some record else none
  | .branch count left right,index => if index<count then left.lookup index else right.lookup (index-count)

theorem checked_size (tree : Tree) (checked : tree.check=true) : tree.toList.length=tree.size := by
  induction tree with
  | leaf record => rfl
  | branch count left right ihl ihr =>
      simp only [Tree.check,Bool.and_eq_true,decide_eq_true_eq] at checked
      simp only [Tree.toList,List.length_append,Tree.size,ihl checked.1.2,ihr checked.2,←checked.1.1]

theorem checked_lookup (tree : Tree) (checked : tree.check=true) (index : Nat) :
    tree.lookup index=tree.toList[index]? := by
  induction tree generalizing index with
  | leaf record =>
      simp only [Tree.lookup,Tree.toList]
      split
      · next equal => subst index; rfl
      · next unequal => cases index with
        | zero => contradiction
        | succ n => rfl
  | branch count left right ihl ihr =>
      simp only [Tree.check,Bool.and_eq_true,decide_eq_true_eq] at checked
      have leftLength : left.toList.length=count := (checked_size left checked.1.2).trans checked.1.1.symm
      simp only [Tree.lookup,Tree.toList]
      split
      · next below => rw [List.getElem?_append_left (by simpa only [leftLength] using below)]; exact ihl checked.1.2 index
      · next above => rw [List.getElem?_append_right (by simpa only [leftLength] using Nat.le_of_not_gt above),leftLength]; exact ihr checked.2 (index-count)

def fuelTree (tree : Tree) (inputTerms : Nat → Linear) : Nat → Nat → Linear
  | 0,_ => []
  | fuel+1,index => match tree.lookup index with
    | none => []
    | some (.constant coefficient) => [(0,coefficient)]
    | some (.input witness) => inputTerms witness
    | some (.add left right) => fuelTree tree inputTerms fuel left ++ fuelTree tree inputTerms fuel right
    | some (.scaleLeft _ right coefficient) => scaleLinear coefficient (fuelTree tree inputTerms fuel right)

theorem fuelTree_agrees (tree : Tree) (records : Array Record)
    (lookup : ∀ i,tree.lookup i=records[i]?) (inputTerms : Nat → Linear) (fuel index : Nat) :
    fuelTree tree inputTerms fuel index=fuelValues records inputTerms fuel index := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
      simp only [fuelTree,fuelValues,lookup]
      cases records[index]? with
      | none => rfl
      | some record => cases record <;> simp only [ih]

theorem tree_node_certificate (p inputs : Nat) (tree : Tree) (records : Array Record)
    (lookup : ∀ i,tree.lookup i=records[i]?) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (assertions : List (Fin records.size × Fin records.size))
    (outputs : List (Fin records.size)) (fuel : Nat) (enough : records.size≤fuel) (index : Fin records.size) :
    NodeCertificate p [] inputTerms
      ((graph inputs records checked assertions outputs).prior
        (fun i => .linear (fuelTree tree inputTerms fuel i.val)) index)
      ((graph inputs records checked assertions outputs).node index)
      (.linear (fuelTree tree inputTerms fuel index.val)) := by
  have same : (fun i : Fin records.size => Expression.linear (fuelTree tree inputTerms fuel i.val)) =
      (fun i => Expression.linear (fuelValues records inputTerms fuel i.val)) := by
    funext i; exact congrArg Expression.linear (fuelTree_agrees tree records lookup inputTerms fuel i.val)
  rw [same,fuelTree_agrees tree records lookup inputTerms fuel index.val]
  exact fuel_node_certificate p inputs records checked inputTerms assertions outputs fuel enough index
end ShielddSecurity.CompilerRecipeTree01
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipeTree01.checked_size
#print axioms ShielddSecurity.CompilerRecipeTree01.checked_size
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipeTree01.checked_lookup
#print axioms ShielddSecurity.CompilerRecipeTree01.checked_lookup
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipeTree01.fuelTree_agrees
#print axioms ShielddSecurity.CompilerRecipeTree01.fuelTree_agrees
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipeTree01.tree_node_certificate
#print axioms ShielddSecurity.CompilerRecipeTree01.tree_node_certificate
