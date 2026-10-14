/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof06
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B06
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows44 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R44.arithmeticRows.toList
theorem actual44 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166789 4 rows44=true := by decide +kernel
theorem step44 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R44.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 44
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R44.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166789 4 rows44 actual44 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R44.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R44.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R44.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R44Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows45 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R45.arithmeticRows.toList
theorem actual45 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166793 4 rows45=true := by decide +kernel
theorem step45 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R45.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 45
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R45.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166793 4 rows45 actual45 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R45.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R45.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R45.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R45Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows46 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R46.arithmeticRows.toList
theorem actual46 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166797 4 rows46=true := by decide +kernel
theorem step46 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R46.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 46
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R46.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166797 4 rows46 actual46 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R46.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R46.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R46.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R46Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows47 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R47.arithmeticRows.toList
theorem actual47 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166801 4 rows47=true := by decide +kernel
theorem step47 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R47.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 47
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R47.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166801 4 rows47 actual47 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R47.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R47.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R47.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R47Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows48 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R48.arithmeticRows.toList
theorem actual48 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166805 4 rows48=true := by decide +kernel
theorem step48 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R48.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 48
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R48.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166805 4 rows48 actual48 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R48.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R48.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R48.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R48Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows49 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R49.arithmeticRows.toList
theorem actual49 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166809 4 rows49=true := by decide +kernel
theorem step49 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R49.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 49
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R49.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166809 4 rows49 actual49 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R49.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R49.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R49.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R49Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows50 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R50.arithmeticRows.toList
theorem actual50 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166813 4 rows50=true := by decide +kernel
theorem step50 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R50.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 50
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R50.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166813 4 rows50 actual50 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R50.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R50.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R50.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R50Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B06
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B06.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual44
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual44
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step44
#print axioms ShielddSecurity.MapAssetHashTail736B06.step44
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual45
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual45
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step45
#print axioms ShielddSecurity.MapAssetHashTail736B06.step45
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual46
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual46
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step46
#print axioms ShielddSecurity.MapAssetHashTail736B06.step46
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual47
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual47
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step47
#print axioms ShielddSecurity.MapAssetHashTail736B06.step47
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual48
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual48
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step48
#print axioms ShielddSecurity.MapAssetHashTail736B06.step48
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual49
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual49
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step49
#print axioms ShielddSecurity.MapAssetHashTail736B06.step49
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.actual50
#print axioms ShielddSecurity.MapAssetHashTail736B06.actual50
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B06.step50
#print axioms ShielddSecurity.MapAssetHashTail736B06.step50
