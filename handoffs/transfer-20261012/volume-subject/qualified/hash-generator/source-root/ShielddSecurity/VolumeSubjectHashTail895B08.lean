/- Generated from maintained volume subject-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeSubjectHashTail895B08
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 23076 396 85432
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows26 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R26.arithmeticRows.toList
theorem actual26 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85930 4 rows26=true := by decide +kernel
theorem step26 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R26.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 26
      (fun i => eval rho (linear ren (TransferPoseidonCall04R26.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85930 4 rows26 actual26 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R26.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R26.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R26.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R26Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows27 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R27.arithmeticRows.toList
theorem actual27 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85934 4 rows27=true := by decide +kernel
theorem step27 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R27.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 27
      (fun i => eval rho (linear ren (TransferPoseidonCall04R27.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85934 4 rows27 actual27 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R27.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R27.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R27.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R27Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows28 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R28.arithmeticRows.toList
theorem actual28 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85938 4 rows28=true := by decide +kernel
theorem step28 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R28.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 28
      (fun i => eval rho (linear ren (TransferPoseidonCall04R28.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85938 4 rows28 actual28 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R28.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R28.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R28.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R28Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.VolumeSubjectHashTail895B08
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.fixed
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.actual26
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.actual26
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.step26
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.step26
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.actual27
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.actual27
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.step27
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.step27
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.actual28
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.actual28
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B08.step28
#print axioms ShielddSecurity.VolumeSubjectHashTail895B08.step28
