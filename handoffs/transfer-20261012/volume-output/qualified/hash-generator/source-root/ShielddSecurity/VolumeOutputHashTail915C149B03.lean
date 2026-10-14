/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof01
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C149B03
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96444
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows11 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R11.arithmeticRows.toList
 theorem actual11 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96882 4 rows11=true := by decide +kernel
 theorem step11 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R11.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 11
       (fun i => eval rho (linear ren (TransferPoseidonCall04R11.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96882 4 rows11 actual11 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R11.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R11.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R11.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R11Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows12 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R12.arithmeticRows.toList
 theorem actual12 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96886 4 rows12=true := by decide +kernel
 theorem step12 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R12.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 12
       (fun i => eval rho (linear ren (TransferPoseidonCall04R12.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96886 4 rows12 actual12 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R12.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R12.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R12.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R12Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows13 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R13.arithmeticRows.toList
 theorem actual13 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96890 4 rows13=true := by decide +kernel
 theorem step13 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R13.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 13
       (fun i => eval rho (linear ren (TransferPoseidonCall04R13.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96890 4 rows13 actual13 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R13.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R13.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R13.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R13Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C149B03
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.actual11
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.actual11
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.step11
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.step11
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.actual12
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.actual12
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.step12
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.step12
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.actual13
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.actual13
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C149B03.step13
#print axioms ShielddSecurity.VolumeOutputHashTail915C149B03.step13
