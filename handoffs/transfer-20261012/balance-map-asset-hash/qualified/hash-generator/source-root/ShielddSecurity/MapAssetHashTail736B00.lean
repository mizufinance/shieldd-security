/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof00
import ShielddSecurity.TransferPoseidonWidth3Call08Proof01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B00
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows2 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R02.arithmeticRows.toList
theorem actual2 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166605 12 rows2=true := by decide +kernel
theorem step2 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R02.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 2
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R02.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166605 12 rows2 actual2 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R02.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R02.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R02.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R02Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows3 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R03.arithmeticRows.toList
theorem actual3 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166617 12 rows3=true := by decide +kernel
theorem step3 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R03.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 3
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R03.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166617 12 rows3 actual3 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R03.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R03.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R03.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R03Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows4 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R04.arithmeticRows.toList
theorem actual4 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166629 4 rows4=true := by decide +kernel
theorem step4 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R04.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 4
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R04.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166629 4 rows4 actual4 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R04.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R04.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R04.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R04Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows5 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R05.arithmeticRows.toList
theorem actual5 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166633 4 rows5=true := by decide +kernel
theorem step5 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R05.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 5
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R05.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166633 4 rows5 actual5 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R05.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R05.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R05.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R05Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows6 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R06.arithmeticRows.toList
theorem actual6 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166637 4 rows6=true := by decide +kernel
theorem step6 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R06.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 6
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R06.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166637 4 rows6 actual6 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R06.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R06.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R06.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R06Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows7 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R07.arithmeticRows.toList
theorem actual7 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166641 4 rows7=true := by decide +kernel
theorem step7 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R07.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 7
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R07.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166641 4 rows7 actual7 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R07.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R07.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R07.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R07Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows8 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R08.arithmeticRows.toList
theorem actual8 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166645 4 rows8=true := by decide +kernel
theorem step8 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R08.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 8
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R08.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166645 4 rows8 actual8 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R08.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R08.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R08.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R08Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B00
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B00.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual2
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual2
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step2
#print axioms ShielddSecurity.MapAssetHashTail736B00.step2
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual3
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual3
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step3
#print axioms ShielddSecurity.MapAssetHashTail736B00.step3
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual4
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual4
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step4
#print axioms ShielddSecurity.MapAssetHashTail736B00.step4
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual5
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual5
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step5
#print axioms ShielddSecurity.MapAssetHashTail736B00.step5
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual6
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual6
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step6
#print axioms ShielddSecurity.MapAssetHashTail736B00.step6
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual7
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual7
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step7
#print axioms ShielddSecurity.MapAssetHashTail736B00.step7
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.actual8
#print axioms ShielddSecurity.MapAssetHashTail736B00.actual8
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B00.step8
#print axioms ShielddSecurity.MapAssetHashTail736B00.step8
