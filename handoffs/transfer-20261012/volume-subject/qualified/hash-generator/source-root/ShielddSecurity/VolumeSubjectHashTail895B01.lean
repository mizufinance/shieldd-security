/- Generated from maintained volume subject-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeSubjectHashTail895B01
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 23076 396 85432
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows5 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R05.arithmeticRows.toList
theorem actual5 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85846 4 rows5=true := by decide +kernel
theorem step5 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R05.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 5
      (fun i => eval rho (linear ren (TransferPoseidonCall04R05.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85846 4 rows5 actual5 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R05.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R05.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R05.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R05Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows6 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R06.arithmeticRows.toList
theorem actual6 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85850 4 rows6=true := by decide +kernel
theorem step6 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R06.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 6
      (fun i => eval rho (linear ren (TransferPoseidonCall04R06.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85850 4 rows6 actual6 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R06.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R06.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R06.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R06Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows7 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R07.arithmeticRows.toList
theorem actual7 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 85854 4 rows7=true := by decide +kernel
theorem step7 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R07.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 7
      (fun i => eval rho (linear ren (TransferPoseidonCall04R07.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 85854 4 rows7 actual7 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R07.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R07.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R07.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R07Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.VolumeSubjectHashTail895B01
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.fixed
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.actual5
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.actual5
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.step5
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.step5
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.actual6
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.actual6
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.step6
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.step6
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.actual7
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.actual7
set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectHashTail895B01.step7
#print axioms ShielddSecurity.VolumeSubjectHashTail895B01.step7
