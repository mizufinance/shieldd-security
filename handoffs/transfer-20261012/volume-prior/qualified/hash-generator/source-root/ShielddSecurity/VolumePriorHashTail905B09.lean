/- Generated from maintained volume prior state-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePriorHashTail905B09
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 23076 396 85854
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows29 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R29.arithmeticRows.toList
theorem actual29 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86364 4 rows29=true := by decide +kernel
theorem step29 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R29.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 29
      (fun i => eval rho (linear ren (TransferPoseidonCall04R29.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86364 4 rows29 actual29 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R29.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R29.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R29.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R29Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows30 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R30.arithmeticRows.toList
theorem actual30 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86368 4 rows30=true := by decide +kernel
theorem step30 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R30.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 30
      (fun i => eval rho (linear ren (TransferPoseidonCall04R30.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86368 4 rows30 actual30 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R30.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R30.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R30.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R30Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows31 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R31.arithmeticRows.toList
theorem actual31 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86372 4 rows31=true := by decide +kernel
theorem step31 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R31.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 31
      (fun i => eval rho (linear ren (TransferPoseidonCall04R31.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86372 4 rows31 actual31 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R31.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R31.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R31.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R31Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.VolumePriorHashTail905B09
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.fixed
#print axioms ShielddSecurity.VolumePriorHashTail905B09.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.actual29
#print axioms ShielddSecurity.VolumePriorHashTail905B09.actual29
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.step29
#print axioms ShielddSecurity.VolumePriorHashTail905B09.step29
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.actual30
#print axioms ShielddSecurity.VolumePriorHashTail905B09.actual30
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.step30
#print axioms ShielddSecurity.VolumePriorHashTail905B09.step30
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.actual31
#print axioms ShielddSecurity.VolumePriorHashTail905B09.actual31
set_option pp.all true in
#check @ShielddSecurity.VolumePriorHashTail905B09.step31
#print axioms ShielddSecurity.VolumePriorHashTail905B09.step31
