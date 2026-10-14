/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof02
import ShielddSecurity.TransferPoseidonWidth3Call08Proof03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B03
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows23 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R23.arithmeticRows.toList
theorem actual23 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166705 4 rows23=true := by decide +kernel
theorem step23 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R23.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 23
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R23.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166705 4 rows23 actual23 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R23.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R23.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R23.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R23Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows24 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R24.arithmeticRows.toList
theorem actual24 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166709 4 rows24=true := by decide +kernel
theorem step24 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R24.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 24
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R24.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166709 4 rows24 actual24 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R24.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R24.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R24.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R24Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows25 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R25.arithmeticRows.toList
theorem actual25 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166713 4 rows25=true := by decide +kernel
theorem step25 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R25.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 25
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R25.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166713 4 rows25 actual25 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R25.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R25.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R25.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R25Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows26 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R26.arithmeticRows.toList
theorem actual26 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166717 4 rows26=true := by decide +kernel
theorem step26 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R26.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 26
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R26.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166717 4 rows26 actual26 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R26.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R26.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R26.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R26Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows27 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R27.arithmeticRows.toList
theorem actual27 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166721 4 rows27=true := by decide +kernel
theorem step27 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R27.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 27
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R27.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166721 4 rows27 actual27 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R27.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R27.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R27.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R27Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows28 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R28.arithmeticRows.toList
theorem actual28 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166725 4 rows28=true := by decide +kernel
theorem step28 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R28.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 28
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R28.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166725 4 rows28 actual28 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R28.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R28.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R28.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R28Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows29 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R29.arithmeticRows.toList
theorem actual29 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166729 4 rows29=true := by decide +kernel
theorem step29 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R29.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 29
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R29.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166729 4 rows29 actual29 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R29.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R29.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R29.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R29Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B03
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B03.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual23
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual23
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step23
#print axioms ShielddSecurity.MapAssetHashTail736B03.step23
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual24
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual24
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step24
#print axioms ShielddSecurity.MapAssetHashTail736B03.step24
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual25
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual25
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step25
#print axioms ShielddSecurity.MapAssetHashTail736B03.step25
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual26
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual26
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step26
#print axioms ShielddSecurity.MapAssetHashTail736B03.step26
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual27
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual27
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step27
#print axioms ShielddSecurity.MapAssetHashTail736B03.step27
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual28
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual28
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step28
#print axioms ShielddSecurity.MapAssetHashTail736B03.step28
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.actual29
#print axioms ShielddSecurity.MapAssetHashTail736B03.actual29
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B03.step29
#print axioms ShielddSecurity.MapAssetHashTail736B03.step29
