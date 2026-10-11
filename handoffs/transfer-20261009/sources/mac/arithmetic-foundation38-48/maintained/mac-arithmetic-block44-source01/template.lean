import ShielddSecurity.CompilerCachedArithmetic42
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerArithmeticBlock44
open Compiler
structure Block (coefficient : Nat → Int) (copy floor length : Nat) where
  tree : CompilerCachedArithmetic42.Tree
  actual : Nat → Option Row
  count_exact : CompilerCachedArithmetic42.count tree=length
  sized : CompilerCachedArithmetic42.sized tree=true
  checked : CompilerCachedArithmetic42.check copy floor tree=true
  actual_exact : ∀ index : Nat,actual index=CompilerCachedArithmetic42.rowAt coefficient floor tree index
noncomputable def leaf (coefficient : Nat → Int) (copy floor length : Nat)
    (recipes : List CompilerIndexedRecipe38.Recipe) (actual : Nat → Option Row)
    (sized : CompilerIndexedRecipe38.span recipes=length)
    (checked : CompilerIndexedRecipe38.check copy floor recipes=true)
    (exactRows : ∀ index : Nat,actual index=(CompilerFreshArithmetic35.rows floor (CompilerIndexedRecipe38.decodeList coefficient recipes))[index]?) :
    Block coefficient copy floor length where
  tree := .leaf length recipes
  actual := actual
  count_exact := rfl
  sized := by exact decide_eq_true sized
  checked := checked
  actual_exact := exactRows
noncomputable def append (coefficient : Nat → Int) (copy floor leftLength rightLength : Nat)
    (left : Block coefficient copy floor leftLength)
    (right : Block coefficient copy (floor+leftLength) rightLength) :
    Block coefficient copy floor (leftLength+rightLength) where
  tree := .append leftLength left.tree right.tree
  actual := fun index => if index<leftLength then left.actual index else right.actual (index-leftLength)
  count_exact := by change leftLength+CompilerCachedArithmetic42.count right.tree=leftLength+rightLength;rw [right.count_exact]
  sized := by
    apply Bool.and_eq_true_iff.mpr
    exact ⟨decide_eq_true left.count_exact,Bool.and_eq_true_iff.mpr ⟨left.sized,right.sized⟩⟩
  checked := Bool.and_eq_true_iff.mpr ⟨left.checked,right.checked⟩
  actual_exact := by
    intro index
    change (if index<leftLength then left.actual index else right.actual (index-leftLength))=
      (if index<leftLength then CompilerCachedArithmetic42.rowAt coefficient floor left.tree index
      else CompilerCachedArithmetic42.rowAt coefficient (floor+leftLength) right.tree (index-leftLength))
    rw [left.actual_exact index,right.actual_exact (index-leftLength)]
theorem every_position (coefficient : Nat → Int) (copy floor length : Nat)
    (block : Block coefficient copy floor length) (index : Nat) (bound : index<length) :
    ∃ row : Row,block.actual index=some row := by
  rw [block.actual_exact]
  exact CompilerCachedArithmetic42.every_position coefficient block.tree block.sized floor index (by rw [block.count_exact];exact bound)
theorem exact_reverse (coefficient : Nat → Int) (copy floor length : Nat)
    (block : Block coefficient copy floor length) (index : Nat) (row : Row) :
    block.actual index=some row ↔ CompilerCachedArithmetic42.rowAt coefficient floor block.tree index=some row := by
  rw [block.actual_exact]
variable {F : Type} [Field F]
noncomputable def completed (coefficient : Nat → Int) (copy floor length : Nat)
    (block : Block coefficient copy floor length) (base : Nat → F) :=
  CompilerCachedArithmetic42.run coefficient block.tree floor base
def SatisfiesAt (rho : Nat → F) (actual : Nat → Option Row) (length : Nat) :=
  ∀ index<length,∀ row : Row,actual index=some row → Square (eval rho row.a) (eval rho row.b)
theorem complete (coefficient : Nat → Int) (copy floor length : Nat)
    (block : Block coefficient copy floor length) (base : Nat → F)
    (below : floor+length≤copy) (four : (4:F)≠0) :
    SatisfiesAt (completed coefficient copy floor length block base) block.actual length := by
  have done:=CompilerCachedArithmetic42.complete coefficient block.tree block.sized copy floor base block.checked
    (by rw [block.count_exact];exact below) four
  intro index bound row found
  apply done index (by rw [block.count_exact];exact bound) row
  rw [←block.actual_exact]
  exact found
theorem outside (coefficient : Nat → Int) (copy floor length : Nat)
    (block : Block coefficient copy floor length) (base : Nat → F) (column : Nat)
    (bound : column<floor ∨ floor+length≤column) :
    completed coefficient copy floor length block base column=base column := by
  exact CompilerCachedArithmetic42.outside coefficient block.tree block.sized floor base column (by rw [block.count_exact];exact bound)
theorem inputs (coefficient : Nat → Int) (copy length : Nat)
    (block : Block coefficient copy 22738 length) (base : Nat → F) (input : Nat) (bound : input<22735) :
    completed coefficient copy 22738 length block base (3+input)=base (3+input) :=
  outside coefficient copy 22738 length block base _ (Or.inl (by omega))
theorem fixed (coefficient : Nat → Int) (copy floor length : Nat)
    (block : Block coefficient copy floor length) (base : Nat → F)
    (lower : 2<floor) (upper : floor+length≤copy) :
    completed coefficient copy floor length block base 0=base 0 ∧
    completed coefficient copy floor length block base 1=base 1 ∧
    completed coefficient copy floor length block base 2=base 2 ∧
    completed coefficient copy floor length block base copy=base copy :=
  ⟨outside coefficient copy floor length block base 0 (Or.inl (by omega)),
   outside coefficient copy floor length block base 1 (Or.inl (by omega)),
   outside coefficient copy floor length block base 2 (Or.inl lower),
   outside coefficient copy floor length block base copy (Or.inr upper)⟩
end ShielddSecurity.CompilerArithmeticBlock44

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.Block
#print axioms ShielddSecurity.CompilerArithmeticBlock44.Block
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.leaf
#print axioms ShielddSecurity.CompilerArithmeticBlock44.leaf
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.append
#print axioms ShielddSecurity.CompilerArithmeticBlock44.append
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.every_position
#print axioms ShielddSecurity.CompilerArithmeticBlock44.every_position
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.exact_reverse
#print axioms ShielddSecurity.CompilerArithmeticBlock44.exact_reverse
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.completed
#print axioms ShielddSecurity.CompilerArithmeticBlock44.completed
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.SatisfiesAt
#print axioms ShielddSecurity.CompilerArithmeticBlock44.SatisfiesAt
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.complete
#print axioms ShielddSecurity.CompilerArithmeticBlock44.complete
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.outside
#print axioms ShielddSecurity.CompilerArithmeticBlock44.outside
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.inputs
#print axioms ShielddSecurity.CompilerArithmeticBlock44.inputs
set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticBlock44.fixed
#print axioms ShielddSecurity.CompilerArithmeticBlock44.fixed
