/- Generated from maintained volume path-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof07
import ShielddSecurity.TransferPoseidonCall04Proof08
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C136B20
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 90946
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows62 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R62.arithmeticRows.toList
 theorem actual62 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 91608 24 rows62=true := by decide +kernel
 theorem step62 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R62.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 62
       (fun i => eval rho (linear ren (TransferPoseidonCall04R62.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 91608 24 rows62 actual62 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R62.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R62.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R62.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R62Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows63 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R63.arithmeticRows.toList
 theorem actual63 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 91632 24 rows63=true := by decide +kernel
 theorem step63 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R63.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 63
       (fun i => eval rho (linear ren (TransferPoseidonCall04R63.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 91632 24 rows63 actual63 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R63.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R63.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R63.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R63Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows64 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R64.arithmeticRows.toList
 theorem actual64 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 91656 24 rows64=true := by decide +kernel
 theorem step64 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R64.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 64
       (fun i => eval rho (linear ren (TransferPoseidonCall04R64.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 91656 24 rows64 actual64 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R64.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R64.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R64.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R64Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C136B20
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.actual62
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.actual62
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.step62
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.step62
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.actual63
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.actual63
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.step63
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.step63
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.actual64
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.actual64
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C136B20.step64
#print axioms ShielddSecurity.VolumePathHashTail928C136B20.step64
