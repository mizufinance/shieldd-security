import ShielddSecurity.RowCompletionRenaming

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.FiniteColumnRenaming

/-- A finite lookup tree. Branch bounds affect lookup, but soundness does not
assume that the authored tree is sorted or that its keys are unique. -/
inductive Tree where
  | empty
  | leaf (source target : Nat)
  | branch (pivot : Nat) (left right : Tree)
  deriving DecidableEq

def entries : Tree → List (Nat × Nat)
  | .empty => []
  | .leaf source target => [(source,target)]
  | .branch _ left right => entries left ++ entries right

def lookup : Tree → Nat → Option Nat
  | .empty, _ => none
  | .leaf source target, column => if column = source then some target else none
  | .branch pivot left right, column =>
      if column < pivot then lookup left column else lookup right column

def column (tree : Tree) (input : Nat) : Nat :=
  match lookup tree input with
  | none => input
  | some output => output

theorem lookup_member (tree : Tree) (input output : Nat)
    (found : lookup tree input = some output) : (input,output) ∈ entries tree := by
  induction tree with
  | empty => simp only [lookup] at found; cases found
  | leaf source target =>
      unfold lookup at found
      split at found
      · rename_i same
        have value := Option.some.inj found
        subst input
        subst output
        exact List.mem_singleton_self _
      · cases found
  | branch pivot left right leftIH rightIH =>
      unfold lookup at found
      split at found
      · exact List.mem_append_left _ (leftIH found)
      · exact List.mem_append_right _ (rightIH found)

/-- Check a bounded subtree against the complete lookup tree. This can be
split into independently checked pages and assembled without an all-pairs
injectivity decision or a wide row-by-write walk. -/
def checkInverse (whole : Tree) : Tree → Bool
  | .empty => true
  | .leaf source target => decide (column whole target = source)
  | .branch _ left right => checkInverse whole left && checkInverse whole right

theorem checked_part (whole part : Tree) (checked : checkInverse whole part = true) :
    ∀ item ∈ entries part, column whole item.2 = item.1 := by
  induction part with
  | empty => intro item member; simp only [entries,List.not_mem_nil] at member
  | leaf source target =>
      intro item member
      have same := List.mem_singleton.mp member
      subst item
      exact of_decide_eq_true checked
  | branch pivot left right leftIH rightIH =>
      have parts : checkInverse whole left = true ∧ checkInverse whole right = true := by
        simpa only [checkInverse,Bool.and_eq_true] using checked
      intro item member
      rcases List.mem_append.mp member with inLeft | inRight
      · exact leftIH parts.1 item inLeft
      · exact rightIH parts.2 item inRight

theorem involutive (tree : Tree) (checked : checkInverse tree tree = true) :
    Function.Involutive (column tree) := by
  intro input
  cases found : lookup tree input with
  | none => simp only [column,found]
  | some output =>
      have inverted := checked_part tree tree checked (input,output)
        (lookup_member tree input output found)
      simpa only [column,found] using inverted

theorem injective (tree : Tree) (checked : checkInverse tree tree = true) :
    Function.Injective (column tree) := (involutive tree checked).injective

theorem outside_entries (tree : Tree) (input : Nat)
    (outside : ∀ item ∈ entries tree, item.1 ≠ input) : column tree input = input := by
  cases found : lookup tree input with
  | none => simp only [column,found]
  | some output =>
      exact False.elim (outside (input,output) (lookup_member tree input output found) rfl)

set_option pp.all true in
#check @lookup_member
#print axioms lookup_member
set_option pp.all true in
#check @checked_part
#print axioms checked_part
set_option pp.all true in
#check @involutive
#print axioms involutive
set_option pp.all true in
#check @injective
#print axioms injective
set_option pp.all true in
#check @outside_entries
#print axioms outside_entries

end ShielddSecurity.FiniteColumnRenaming
