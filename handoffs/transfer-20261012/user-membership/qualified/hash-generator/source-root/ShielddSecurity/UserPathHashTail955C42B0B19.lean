/- Generated from maintained user path-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof07
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.UserPathHashTail955C42B0B19
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 21020
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows59 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R59.arithmeticRows.toList
 theorem actual59 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 21650 4 rows59=true := by decide +kernel
 theorem step59 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R59.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 59
       (fun i => eval rho (linear ren (TransferPoseidonCall04R59.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 21650 4 rows59 actual59 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R59.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R59.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R59.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R59Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows60 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R60.arithmeticRows.toList
 theorem actual60 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 21654 4 rows60=true := by decide +kernel
 theorem step60 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R60.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 60
       (fun i => eval rho (linear ren (TransferPoseidonCall04R60.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 21654 4 rows60 actual60 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R60.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R60.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R60.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R60Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows61 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R61.arithmeticRows.toList
 theorem actual61 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 21658 24 rows61=true := by decide +kernel
 theorem step61 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R61.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 61
       (fun i => eval rho (linear ren (TransferPoseidonCall04R61.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 21658 24 rows61 actual61 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R61.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R61.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R61.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R61Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.UserPathHashTail955C42B0B19
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.fixed
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.fixed
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.actual59
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.actual59
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.step59
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.step59
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.actual60
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.actual60
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.step60
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.step60
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.actual61
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.actual61
set_option pp.all true in
#check @ShielddSecurity.UserPathHashTail955C42B0B19.step61
#print axioms ShielddSecurity.UserPathHashTail955C42B0B19.step61
