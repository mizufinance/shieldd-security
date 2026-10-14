/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof05
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C151B13
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 97266
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows41 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R41.arithmeticRows.toList
 theorem actual41 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97824 4 rows41=true := by decide +kernel
 theorem step41 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R41.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 41
       (fun i => eval rho (linear ren (TransferPoseidonCall04R41.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97824 4 rows41 actual41 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R41.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R41.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R41.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R41Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows42 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R42.arithmeticRows.toList
 theorem actual42 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97828 4 rows42=true := by decide +kernel
 theorem step42 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R42.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 42
       (fun i => eval rho (linear ren (TransferPoseidonCall04R42.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97828 4 rows42 actual42 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R42.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R42.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R42.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R42Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows43 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R43.arithmeticRows.toList
 theorem actual43 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97832 4 rows43=true := by decide +kernel
 theorem step43 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R43.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 43
       (fun i => eval rho (linear ren (TransferPoseidonCall04R43.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97832 4 rows43 actual43 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R43.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R43.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R43.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R43Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C151B13
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.actual41
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.actual41
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.step41
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.step41
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.actual42
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.actual42
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.step42
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.step42
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.actual43
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.actual43
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B13.step43
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B13.step43
