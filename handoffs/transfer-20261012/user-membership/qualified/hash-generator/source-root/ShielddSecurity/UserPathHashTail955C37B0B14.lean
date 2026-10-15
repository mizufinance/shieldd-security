/- Generated from maintained user path-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof05
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.UserPathHashTail955C37B0B14
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 18154
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows44 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R44.arithmeticRows.toList
 theorem actual44 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 18724 4 rows44=true := by decide +kernel
 theorem step44 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R44.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 44
       (fun i => eval rho (linear ren (TransferPoseidonCall04R44.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 18724 4 rows44 actual44 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R44.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R44.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R44.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R44Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows45 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R45.arithmeticRows.toList
 theorem actual45 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 18728 4 rows45=true := by decide +kernel
 theorem step45 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R45.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 45
       (fun i => eval rho (linear ren (TransferPoseidonCall04R45.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 18728 4 rows45 actual45 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R45.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R45.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R45.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R45Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows46 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R46.arithmeticRows.toList
 theorem actual46 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 18732 4 rows46=true := by decide +kernel
 theorem step46 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R46.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 46
       (fun i => eval rho (linear ren (TransferPoseidonCall04R46.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 18732 4 rows46 actual46 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R46.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R46.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R46.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R46Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.UserPathHashTail955C37B0B14
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.fixed
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.fixed
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.actual44
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.actual44
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.step44
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.step44
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.actual45
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.actual45
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.step45
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.step45
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.actual46
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.actual46
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C37B0B14.step46
#print axioms ShielddSecurity.UserPathHashTail955C37B0B14.step46
