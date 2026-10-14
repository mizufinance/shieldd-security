/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof05
import ShielddSecurity.TransferPoseidonCall04Proof06
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C149B15
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96444
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows47 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R47.arithmeticRows.toList
 theorem actual47 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97026 4 rows47=true := by decide +kernel
 theorem step47 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R47.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 47
       (fun i => eval rho (linear ren (TransferPoseidonCall04R47.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97026 4 rows47 actual47 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R47.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R47.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R47.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R47Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows48 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R48.arithmeticRows.toList
 theorem actual48 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97030 4 rows48=true := by decide +kernel
 theorem step48 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R48.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 48
       (fun i => eval rho (linear ren (TransferPoseidonCall04R48.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97030 4 rows48 actual48 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R48.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R48.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R48.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R48Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows49 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R49.arithmeticRows.toList
 theorem actual49 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97034 4 rows49=true := by decide +kernel
 theorem step49 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R49.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 49
       (fun i => eval rho (linear ren (TransferPoseidonCall04R49.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97034 4 rows49 actual49 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R49.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R49.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R49.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R49Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C149B15
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.actual47
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.actual47
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.step47
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.step47
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.actual48
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.actual48
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.step48
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.step48
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.actual49
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.actual49
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B15.step49
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B15.step49
