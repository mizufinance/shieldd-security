/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof02
import ShielddSecurity.TransferPoseidonCall04Proof03
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C149B07
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96444
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows23 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R23.arithmeticRows.toList
 theorem actual23 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96930 4 rows23=true := by decide +kernel
 theorem step23 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R23.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 23
       (fun i => eval rho (linear ren (TransferPoseidonCall04R23.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96930 4 rows23 actual23 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R23.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R23.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R23.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R23Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows24 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R24.arithmeticRows.toList
 theorem actual24 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96934 4 rows24=true := by decide +kernel
 theorem step24 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R24.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 24
       (fun i => eval rho (linear ren (TransferPoseidonCall04R24.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96934 4 rows24 actual24 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R24.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R24.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R24.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R24Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows25 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R25.arithmeticRows.toList
 theorem actual25 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96938 4 rows25=true := by decide +kernel
 theorem step25 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R25.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 25
       (fun i => eval rho (linear ren (TransferPoseidonCall04R25.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96938 4 rows25 actual25 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R25.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R25.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R25.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R25Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C149B07
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.actual23
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.actual23
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.step23
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.step23
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.actual24
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.actual24
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.step24
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.step24
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.actual25
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.actual25
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B07.step25
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B07.step25
