import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof04
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationWideTail525C55B0B10
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
def ren := CompilerWindowRenaming05.swap 23076 396 26728
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def rows32 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R32.arithmeticRows.toList
theorem actual32 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 27250 4 rows32=true := by decide +kernel
theorem step32 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R32.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 32
      (fun i => eval rho (linear ren (TransferPoseidonCall04R32.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 27250 4 rows32 actual32 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R32.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R32.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R32.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R32Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows33 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R33.arithmeticRows.toList
theorem actual33 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 27254 4 rows33=true := by decide +kernel
theorem step33 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R33.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 33
      (fun i => eval rho (linear ren (TransferPoseidonCall04R33.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 27254 4 rows33 actual33 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R33.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R33.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R33.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R33Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
def rows34 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R34.arithmeticRows.toList
theorem actual34 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 27258 4 rows34=true := by decide +kernel
theorem step34 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonCall04R34.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 34
      (fun i => eval rho (linear ren (TransferPoseidonCall04R34.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 27258 4 rows34 actual34 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonCall04R34.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R34.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R34.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonCall04R34Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.AuthorizationWideTail525C55B0B10
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.fixed
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.fixed
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.actual32
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.actual32
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.step32
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.step32
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.actual33
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.actual33
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.step33
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.step33
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.actual34
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.actual34
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWideTail525C55B0B10.step34
#print axioms ShielddSecurity.AuthorizationWideTail525C55B0B10.step34
