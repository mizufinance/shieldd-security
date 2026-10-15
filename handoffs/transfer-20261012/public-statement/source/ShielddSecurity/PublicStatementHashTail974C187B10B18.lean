/- Generated from maintained public statement-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof07
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.PublicStatementHashTail974C187B10B18
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 176380
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows56 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R56.arithmeticRows.toList
 theorem actual56 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 176998 4 rows56=true := by decide +kernel
 theorem step56 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R56.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 56
       (fun i => eval rho (linear ren (TransferPoseidonCall04R56.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 176998 4 rows56 actual56 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R56.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R56.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R56.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R56Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows57 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R57.arithmeticRows.toList
 theorem actual57 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 177002 4 rows57=true := by decide +kernel
 theorem step57 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R57.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 57
       (fun i => eval rho (linear ren (TransferPoseidonCall04R57.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 177002 4 rows57 actual57 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R57.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R57.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R57.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R57Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows58 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R58.arithmeticRows.toList
 theorem actual58 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 177006 4 rows58=true := by decide +kernel
 theorem step58 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R58.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 58
       (fun i => eval rho (linear ren (TransferPoseidonCall04R58.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 177006 4 rows58 actual58 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R58.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R58.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R58.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R58Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.PublicStatementHashTail974C187B10B18
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.fixed
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.fixed
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.actual56
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.actual56
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.step56
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.step56
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.actual57
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.actual57
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.step57
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.step57
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.actual58
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.actual58
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B10B18.step58
#print axioms ShielddSecurity.PublicStatementHashTail974C187B10B18.step58
