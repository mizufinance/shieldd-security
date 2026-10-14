/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof04
import ShielddSecurity.TransferPoseidonCall04Proof05
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C153B12
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 98082
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows38 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R38.arithmeticRows.toList
 theorem actual38 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98628 4 rows38=true := by decide +kernel
 theorem step38 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R38.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 38
       (fun i => eval rho (linear ren (TransferPoseidonCall04R38.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98628 4 rows38 actual38 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R38.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R38.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R38.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R38Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows39 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R39.arithmeticRows.toList
 theorem actual39 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98632 4 rows39=true := by decide +kernel
 theorem step39 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R39.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 39
       (fun i => eval rho (linear ren (TransferPoseidonCall04R39.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98632 4 rows39 actual39 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R39.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R39.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R39.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R39Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows40 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R40.arithmeticRows.toList
 theorem actual40 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98636 4 rows40=true := by decide +kernel
 theorem step40 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R40.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 40
       (fun i => eval rho (linear ren (TransferPoseidonCall04R40.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98636 4 rows40 actual40 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R40.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R40.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R40.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R40Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C153B12
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.actual38
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.actual38
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.step38
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.step38
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.actual39
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.actual39
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.step39
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.step39
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.actual40
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.actual40
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C153B12.step40
#print axioms ShielddSecurity.VolumeOutputHashTail915C153B12.step40
