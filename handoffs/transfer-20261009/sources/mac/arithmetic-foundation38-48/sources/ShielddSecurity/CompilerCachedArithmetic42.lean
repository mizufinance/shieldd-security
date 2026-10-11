import ShielddSecurity.CompilerIndexedRecipe38
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerCachedArithmetic42
open Compiler
inductive Tree where
  | leaf (count : Nat) (recipes : List CompilerIndexedRecipe38.Recipe)
  | append (leftCount : Nat) (left right : Tree)
def count : Tree → Nat
  | .leaf length _ => length
  | .append leftCount _ right => leftCount+count right
def sized : Tree → Bool
  | .leaf length recipes => decide (CompilerIndexedRecipe38.span recipes=length)
  | .append leftCount left right => decide (count left=leftCount) && (sized left && sized right)
def decode (coefficient : Nat → Int) : Tree → CompilerArithmeticForest37.Program
  | .leaf _ recipes => .leaf (CompilerIndexedRecipe38.decodeList coefficient recipes)
  | .append _ left right => .append (decode coefficient left) (decode coefficient right)
def check (copy floor : Nat) : Tree → Bool
  | .leaf _ recipes => CompilerIndexedRecipe38.check copy floor recipes
  | .append leftCount left right => check copy floor left && check copy (floor+leftCount) right
def rowAt (coefficient : Nat → Int) (floor : Nat) : Tree → Nat → Option Row
  | .leaf _ recipes,index => (CompilerFreshArithmetic35.rows floor (CompilerIndexedRecipe38.decodeList coefficient recipes))[index]?
  | .append leftCount left right,index =>
    if index<leftCount then rowAt coefficient floor left index else rowAt coefficient (floor+leftCount) right (index-leftCount)
theorem decode_span (coefficient : Nat → Int) (tree : Tree) (valid : sized tree=true) :
    CompilerArithmeticForest37.span (decode coefficient tree)=count tree := by
  induction tree with
  | leaf length recipes =>
    change CompilerFreshArithmetic35.span (CompilerIndexedRecipe38.decodeList coefficient recipes)=length
    rw [CompilerIndexedRecipe38.decode_span]
    exact of_decide_eq_true valid
  | append leftCount left right ihLeft ihRight =>
    have parts:=Bool.and_eq_true_iff.mp valid
    have children:=Bool.and_eq_true_iff.mp parts.2
    have leftSize : count left=leftCount := of_decide_eq_true parts.1
    change CompilerArithmeticForest37.span (decode coefficient left)+CompilerArithmeticForest37.span (decode coefficient right)=leftCount+count right
    rw [ihLeft children.1,ihRight children.2,leftSize]
theorem decode_check (coefficient : Nat → Int) (tree : Tree) (valid : sized tree=true) (copy floor : Nat) :
    CompilerArithmeticForest37.check copy floor (decode coefficient tree)=check copy floor tree := by
  induction tree generalizing floor with
  | leaf length recipes => exact CompilerIndexedRecipe38.decode_list_check coefficient copy floor recipes
  | append leftCount left right ihLeft ihRight =>
    have parts:=Bool.and_eq_true_iff.mp valid
    have children:=Bool.and_eq_true_iff.mp parts.2
    have leftSize : CompilerArithmeticForest37.span (decode coefficient left)=leftCount :=
      (decode_span coefficient left children.1).trans (of_decide_eq_true parts.1)
    change (CompilerArithmeticForest37.check copy floor (decode coefficient left) &&
      CompilerArithmeticForest37.check copy (floor+CompilerArithmeticForest37.span (decode coefficient left)) (decode coefficient right)) =
      (check copy floor left && check copy (floor+leftCount) right)
    rw [leftSize,ihLeft children.1,ihRight children.2]
theorem rowAt_eq (coefficient : Nat → Int) (tree : Tree) (valid : sized tree=true) (floor index : Nat) :
    rowAt coefficient floor tree index=CompilerArithmeticForest37.rowAt floor (decode coefficient tree) index := by
  induction tree generalizing floor index with
  | leaf length recipes => rfl
  | append leftCount left right ihLeft ihRight =>
    have parts:=Bool.and_eq_true_iff.mp valid
    have children:=Bool.and_eq_true_iff.mp parts.2
    have leftSize : CompilerArithmeticForest37.span (decode coefficient left)=leftCount :=
      (decode_span coefficient left children.1).trans (of_decide_eq_true parts.1)
    change (if index<leftCount then rowAt coefficient floor left index else rowAt coefficient (floor+leftCount) right (index-leftCount)) =
      (if index<CompilerArithmeticForest37.span (decode coefficient left) then CompilerArithmeticForest37.rowAt floor (decode coefficient left) index
      else CompilerArithmeticForest37.rowAt (floor+CompilerArithmeticForest37.span (decode coefficient left)) (decode coefficient right) (index-CompilerArithmeticForest37.span (decode coefficient left)))
    rw [leftSize,ihLeft children.1,ihRight children.2]
theorem every_position (coefficient : Nat → Int) (tree : Tree) (valid : sized tree=true) (floor index : Nat)
    (bound : index<count tree) : ∃ row : Row,rowAt coefficient floor tree index=some row := by
  rw [rowAt_eq coefficient tree valid floor index]
  apply CompilerArithmeticForest37.every_position
  rw [decode_span coefficient tree valid]
  exact bound
variable {F : Type} [Field F]
def run (coefficient : Nat → Int) (tree : Tree) (floor : Nat) (base : Nat → F) :=
  CompilerArithmeticForest37.run floor base (decode coefficient tree)
def SatisfiesAt (rho : Nat → F) (coefficient : Nat → Int) (tree : Tree) (floor : Nat) : Prop :=
  ∀ index<count tree,∀ row : Row,rowAt coefficient floor tree index=some row → Square (eval rho row.a) (eval rho row.b)
theorem complete (coefficient : Nat → Int) (tree : Tree) (valid : sized tree=true) (copy floor : Nat) (base : Nat → F)
    (checked : check copy floor tree=true) (below : floor+count tree≤copy) (four : (4:F)≠0) :
    SatisfiesAt (run coefficient tree floor base) coefficient tree floor := by
  have done:=CompilerArithmeticForest37.complete_indexed (decode coefficient tree) copy floor base
    (by rw [decode_check coefficient tree valid];exact checked) (by rw [decode_span coefficient tree valid];exact below) four
  intro index bound row found
  apply done index (by rw [decode_span coefficient tree valid];exact bound) row
  rw [←rowAt_eq coefficient tree valid floor index]
  exact found
theorem outside (coefficient : Nat → Int) (tree : Tree) (valid : sized tree=true) (floor : Nat) (base : Nat → F) (column : Nat)
    (bound : column<floor ∨ floor+count tree≤column) : run coefficient tree floor base column=base column := by
  apply CompilerArithmeticForest37.outside
  rw [decode_span coefficient tree valid]
  exact bound
end ShielddSecurity.CompilerCachedArithmetic42
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.Tree
#print axioms ShielddSecurity.CompilerCachedArithmetic42.Tree
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.count
#print axioms ShielddSecurity.CompilerCachedArithmetic42.count
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.sized
#print axioms ShielddSecurity.CompilerCachedArithmetic42.sized
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.decode
#print axioms ShielddSecurity.CompilerCachedArithmetic42.decode
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.check
#print axioms ShielddSecurity.CompilerCachedArithmetic42.check
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.rowAt
#print axioms ShielddSecurity.CompilerCachedArithmetic42.rowAt
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.decode_span
#print axioms ShielddSecurity.CompilerCachedArithmetic42.decode_span
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.decode_check
#print axioms ShielddSecurity.CompilerCachedArithmetic42.decode_check
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.rowAt_eq
#print axioms ShielddSecurity.CompilerCachedArithmetic42.rowAt_eq
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.every_position
#print axioms ShielddSecurity.CompilerCachedArithmetic42.every_position
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.run
#print axioms ShielddSecurity.CompilerCachedArithmetic42.run
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.SatisfiesAt
#print axioms ShielddSecurity.CompilerCachedArithmetic42.SatisfiesAt
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.complete
#print axioms ShielddSecurity.CompilerCachedArithmetic42.complete
set_option pp.all true in
#check @ShielddSecurity.CompilerCachedArithmetic42.outside
#print axioms ShielddSecurity.CompilerCachedArithmetic42.outside
