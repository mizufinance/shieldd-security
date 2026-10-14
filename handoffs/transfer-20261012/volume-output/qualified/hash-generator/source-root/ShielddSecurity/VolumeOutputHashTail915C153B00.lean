/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof00
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C153B00
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 98082
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows2 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R02.arithmeticRows.toList
 theorem actual2 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98444 24 rows2=true := by decide +kernel
 theorem step2 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R02.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 2
       (fun i => eval rho (linear ren (TransferPoseidonCall04R02.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98444 24 rows2 actual2 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R02.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R02.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R02.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R02Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows3 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R03.arithmeticRows.toList
 theorem actual3 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98468 24 rows3=true := by decide +kernel
 theorem step3 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R03.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 3
       (fun i => eval rho (linear ren (TransferPoseidonCall04R03.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98468 24 rows3 actual3 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R03.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R03.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R03.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R03Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows4 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R04.arithmeticRows.toList
 theorem actual4 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98492 4 rows4=true := by decide +kernel
 theorem step4 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R04.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 4
       (fun i => eval rho (linear ren (TransferPoseidonCall04R04.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98492 4 rows4 actual4 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R04.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R04.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R04.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R04Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C153B00
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.actual2
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.actual2
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.step2
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.step2
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.actual3
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.actual3
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.step3
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.step3
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.actual4
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.actual4
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B00.step4
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B00.step4
