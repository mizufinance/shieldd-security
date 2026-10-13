import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof06
import ShielddSecurity.TransferPoseidonWidth3Call08Proof07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationNarrowTail523B07
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
def ren := CompilerWindowRenaming05.swap 24732 312 36886
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def rows51 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R51.arithmeticRows.toList
theorem actual51 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39104 4 rows51=true := by decide +kernel
theorem step51 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R51.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 51
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R51.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39104 4 rows51 actual51 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R51.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R51.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R51.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R51Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows52 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R52.arithmeticRows.toList
theorem actual52 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39108 4 rows52=true := by decide +kernel
theorem step52 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R52.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 52
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R52.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39108 4 rows52 actual52 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R52.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R52.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R52.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R52Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows53 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R53.arithmeticRows.toList
theorem actual53 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39112 4 rows53=true := by decide +kernel
theorem step53 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R53.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 53
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R53.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39112 4 rows53 actual53 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R53.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R53.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R53.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R53Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows54 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R54.arithmeticRows.toList
theorem actual54 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39116 4 rows54=true := by decide +kernel
theorem step54 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R54.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 54
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R54.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39116 4 rows54 actual54 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R54.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R54.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R54.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R54Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows55 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R55.arithmeticRows.toList
theorem actual55 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39120 4 rows55=true := by decide +kernel
theorem step55 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R55.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 55
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R55.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39120 4 rows55 actual55 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R55.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R55.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R55.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R55Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows56 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R56.arithmeticRows.toList
theorem actual56 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39124 4 rows56=true := by decide +kernel
theorem step56 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R56.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 56
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R56.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39124 4 rows56 actual56 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R56.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R56.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R56.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R56Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows57 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R57.arithmeticRows.toList
theorem actual57 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39128 4 rows57=true := by decide +kernel
theorem step57 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R57.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 57
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R57.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39128 4 rows57 actual57 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R57.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R57.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R57.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R57Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.AuthorizationNarrowTail523B07
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.fixed
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.fixed
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual51
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual51
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step51
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step51
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual52
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual52
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step52
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step52
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual53
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual53
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step53
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step53
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual54
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual54
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step54
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step54
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual55
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual55
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step55
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step55
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual56
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual56
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step56
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step56
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.actual57
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.actual57
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B07.step57
#print axioms ShielddSecurity.AuthorizationNarrowTail523B07.step57
