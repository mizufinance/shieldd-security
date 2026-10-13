import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof02
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationWideTail525C56B1B05
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
def ren := CompilerWindowRenaming05.swap 23076 396 38142
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def rows17 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R17.arithmeticRows.toList
theorem actual17 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38604 4 rows17=true := by decide +kernel
theorem step17 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R17.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 17
      (fun i => eval rho (linear ren (TransferPoseidonCall04R17.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38604 4 rows17 actual17 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R17.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R17.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R17.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R17Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows18 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R18.arithmeticRows.toList
theorem actual18 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38608 4 rows18=true := by decide +kernel
theorem step18 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R18.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 18
      (fun i => eval rho (linear ren (TransferPoseidonCall04R18.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38608 4 rows18 actual18 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R18.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R18.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R18.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R18Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows19 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R19.arithmeticRows.toList
theorem actual19 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 38612 4 rows19=true := by decide +kernel
theorem step19 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R19.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 19
      (fun i => eval rho (linear ren (TransferPoseidonCall04R19.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 38612 4 rows19 actual19 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R19.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R19.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R19.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R19Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.AuthorizationWideTail525C56B1B05
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.fixed
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.fixed
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.actual17
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.actual17
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.step17
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.step17
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.actual18
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.actual18
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.step18
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.step18
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.actual19
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.actual19
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C56B1B05.step19
#print axioms ShielddSecurity.AuthorizationWideTail525C56B1B05.step19
