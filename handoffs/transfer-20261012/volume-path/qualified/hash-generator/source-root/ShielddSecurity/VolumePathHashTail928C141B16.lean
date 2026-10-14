/- Generated from maintained volume path-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof06
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C141B16
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 93066
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows50 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R50.arithmeticRows.toList
 theorem actual50 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 93660 4 rows50=true := by decide +kernel
 theorem step50 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R50.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 50
       (fun i => eval rho (linear ren (TransferPoseidonCall04R50.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 93660 4 rows50 actual50 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R50.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R50.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R50.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R50Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows51 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R51.arithmeticRows.toList
 theorem actual51 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 93664 4 rows51=true := by decide +kernel
 theorem step51 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R51.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 51
       (fun i => eval rho (linear ren (TransferPoseidonCall04R51.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 93664 4 rows51 actual51 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R51.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R51.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R51.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R51Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows52 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R52.arithmeticRows.toList
 theorem actual52 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 93668 4 rows52=true := by decide +kernel
 theorem step52 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R52.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 52
       (fun i => eval rho (linear ren (TransferPoseidonCall04R52.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 93668 4 rows52 actual52 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R52.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R52.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R52.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R52Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C141B16
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.actual50
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.actual50
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.step50
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.step50
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.actual51
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.actual51
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.step51
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.step51
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.actual52
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.actual52
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C141B16.step52
#print axioms ShielddSecurity.VolumePathHashTail928C141B16.step52
