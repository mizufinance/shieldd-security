/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof01
import ShielddSecurity.TransferPoseidonCall04Proof02
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C151B04
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 97266
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows14 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R14.arithmeticRows.toList
 theorem actual14 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97716 4 rows14=true := by decide +kernel
 theorem step14 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R14.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 14
       (fun i => eval rho (linear ren (TransferPoseidonCall04R14.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97716 4 rows14 actual14 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R14.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R14.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R14.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R14Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows15 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R15.arithmeticRows.toList
 theorem actual15 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97720 4 rows15=true := by decide +kernel
 theorem step15 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R15.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 15
       (fun i => eval rho (linear ren (TransferPoseidonCall04R15.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97720 4 rows15 actual15 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R15.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R15.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R15.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R15Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows16 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R16.arithmeticRows.toList
 theorem actual16 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 97724 4 rows16=true := by decide +kernel
 theorem step16 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R16.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 16
       (fun i => eval rho (linear ren (TransferPoseidonCall04R16.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 97724 4 rows16 actual16 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R16.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R16.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R16.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R16Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C151B04
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.actual14
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.actual14
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.step14
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.step14
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.actual15
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.actual15
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.step15
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.step15
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.actual16
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.actual16
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C151B04.step16
#print axioms ShielddSecurity.VolumeOutputHashTail915C151B04.step16
