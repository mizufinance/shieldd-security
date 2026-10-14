/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof02
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C151B06
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 97266
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows20 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R20.arithmeticRows.toList
 theorem actual20 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97740 4 rows20=true := by decide +kernel
 theorem step20 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R20.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 20
       (fun i => eval rho (linear ren (TransferPoseidonCall04R20.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97740 4 rows20 actual20 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R20.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R20.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R20.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R20Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows21 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R21.arithmeticRows.toList
 theorem actual21 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97744 4 rows21=true := by decide +kernel
 theorem step21 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R21.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 21
       (fun i => eval rho (linear ren (TransferPoseidonCall04R21.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97744 4 rows21 actual21 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R21.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R21.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R21.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R21Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows22 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R22.arithmeticRows.toList
 theorem actual22 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97748 4 rows22=true := by decide +kernel
 theorem step22 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R22.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 22
       (fun i => eval rho (linear ren (TransferPoseidonCall04R22.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97748 4 rows22 actual22 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R22.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R22.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R22.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R22Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C151B06
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.actual20
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.actual20
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.step20
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.step20
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.actual21
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.actual21
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.step21
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.step21
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.actual22
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.actual22
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B06.step22
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B06.step22
