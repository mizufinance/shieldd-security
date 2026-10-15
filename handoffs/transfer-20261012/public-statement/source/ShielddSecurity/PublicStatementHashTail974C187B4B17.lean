/- Generated from maintained public statement-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof06
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.PublicStatementHashTail974C187B4B17
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 173860
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows53 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R53.arithmeticRows.toList
 theorem actual53 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 174466 4 rows53=true := by decide +kernel
 theorem step53 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R53.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 53
       (fun i => eval rho (linear ren (TransferPoseidonCall04R53.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 174466 4 rows53 actual53 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R53.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R53.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R53.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R53Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows54 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R54.arithmeticRows.toList
 theorem actual54 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 174470 4 rows54=true := by decide +kernel
 theorem step54 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R54.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 54
       (fun i => eval rho (linear ren (TransferPoseidonCall04R54.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 174470 4 rows54 actual54 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R54.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R54.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R54.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R54Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows55 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R55.arithmeticRows.toList
 theorem actual55 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 174474 4 rows55=true := by decide +kernel
 theorem step55 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R55.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 55
       (fun i => eval rho (linear ren (TransferPoseidonCall04R55.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 174474 4 rows55 actual55 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R55.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R55.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R55.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R55Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.PublicStatementHashTail974C187B4B17
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.fixed
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.fixed
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.actual53
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.actual53
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.step53
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.step53
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.actual54
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.actual54
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.step54
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.step54
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.actual55
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.actual55
set_option pp.all true in
#check @ShielddSecurity.PublicStatementHashTail974C187B4B17.step55
#print axioms ShielddSecurity.PublicStatementHashTail974C187B4B17.step55
