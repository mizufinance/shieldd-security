import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationNarrowTail523B01
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
def ren := CompilerWindowRenaming05.swap 24732 312 36886
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def rows9 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R09.arithmeticRows.toList
theorem actual9 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38936 4 rows9=true := by decide +kernel
theorem step9 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R09.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 9
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R09.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38936 4 rows9 actual9 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R09.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R09.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R09.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R09Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows10 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R10.arithmeticRows.toList
theorem actual10 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38940 4 rows10=true := by decide +kernel
theorem step10 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R10.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 10
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R10.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38940 4 rows10 actual10 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R10.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R10.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R10.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R10Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows11 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R11.arithmeticRows.toList
theorem actual11 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38944 4 rows11=true := by decide +kernel
theorem step11 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R11.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 11
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R11.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38944 4 rows11 actual11 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R11.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R11.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R11.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R11Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows12 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R12.arithmeticRows.toList
theorem actual12 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38948 4 rows12=true := by decide +kernel
theorem step12 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R12.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 12
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R12.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38948 4 rows12 actual12 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R12.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R12.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R12.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R12Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows13 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R13.arithmeticRows.toList
theorem actual13 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38952 4 rows13=true := by decide +kernel
theorem step13 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R13.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 13
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R13.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38952 4 rows13 actual13 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R13.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R13.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R13.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R13Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows14 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R14.arithmeticRows.toList
theorem actual14 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38956 4 rows14=true := by decide +kernel
theorem step14 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R14.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 14
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R14.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38956 4 rows14 actual14 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R14.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R14.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R14.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R14Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows15 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R15.arithmeticRows.toList
theorem actual15 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38960 4 rows15=true := by decide +kernel
theorem step15 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R15.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 15
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R15.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38960 4 rows15 actual15 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R15.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R15.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R15.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R15Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.AuthorizationNarrowTail523B01
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.fixed
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.fixed
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual9
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual9
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step9
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step9
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual10
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual10
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step10
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step10
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual11
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual11
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step11
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step11
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual12
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual12
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step12
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step12
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual13
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual13
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step13
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step13
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual14
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual14
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step14
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step14
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.actual15
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.actual15
set_option pp.all true in
#check @ShielddSecurity.AuthorizationNarrowTail523B01.step15
#print axioms ShielddSecurity.AuthorizationNarrowTail523B01.step15
