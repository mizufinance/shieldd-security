/- Generated from maintained volume prior state-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePriorHashTail905B02
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 23076 396 85854
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows8 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R08.arithmeticRows.toList
theorem actual8 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86280 4 rows8=true := by decide +kernel
theorem step8 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R08.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 8
      (fun i => eval rho (linear ren (TransferPoseidonCall04R08.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86280 4 rows8 actual8 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R08.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R08.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R08.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R08Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows9 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R09.arithmeticRows.toList
theorem actual9 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86284 4 rows9=true := by decide +kernel
theorem step9 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R09.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 9
      (fun i => eval rho (linear ren (TransferPoseidonCall04R09.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86284 4 rows9 actual9 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R09.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R09.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R09.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R09Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows10 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R10.arithmeticRows.toList
theorem actual10 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86288 4 rows10=true := by decide +kernel
theorem step10 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R10.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 10
      (fun i => eval rho (linear ren (TransferPoseidonCall04R10.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86288 4 rows10 actual10 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R10.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R10.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R10.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R10Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.VolumePriorHashTail905B02
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.fixed
#print axioms ShielddSecurity.VolumePriorHashTail905B02.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.actual8
#print axioms ShielddSecurity.VolumePriorHashTail905B02.actual8
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.step8
#print axioms ShielddSecurity.VolumePriorHashTail905B02.step8
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.actual9
#print axioms ShielddSecurity.VolumePriorHashTail905B02.actual9
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.step9
#print axioms ShielddSecurity.VolumePriorHashTail905B02.step9
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.actual10
#print axioms ShielddSecurity.VolumePriorHashTail905B02.actual10
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B02.step10
#print axioms ShielddSecurity.VolumePriorHashTail905B02.step10
