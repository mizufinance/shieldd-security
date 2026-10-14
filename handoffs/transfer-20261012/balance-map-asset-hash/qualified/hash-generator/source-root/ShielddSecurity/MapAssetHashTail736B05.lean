/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof04
import ShielddSecurity.TransferPoseidonWidth3Call08Proof05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B05
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows37 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R37.arithmeticRows.toList
theorem actual37 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166761 4 rows37=true := by decide +kernel
theorem step37 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R37.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 37
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R37.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166761 4 rows37 actual37 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R37.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R37.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R37.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R37Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows38 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R38.arithmeticRows.toList
theorem actual38 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166765 4 rows38=true := by decide +kernel
theorem step38 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R38.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 38
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R38.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166765 4 rows38 actual38 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R38.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R38.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R38.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R38Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows39 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R39.arithmeticRows.toList
theorem actual39 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166769 4 rows39=true := by decide +kernel
theorem step39 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R39.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 39
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R39.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166769 4 rows39 actual39 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R39.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R39.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R39.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R39Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows40 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R40.arithmeticRows.toList
theorem actual40 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166773 4 rows40=true := by decide +kernel
theorem step40 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R40.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 40
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R40.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166773 4 rows40 actual40 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R40.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R40.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R40.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R40Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows41 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R41.arithmeticRows.toList
theorem actual41 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166777 4 rows41=true := by decide +kernel
theorem step41 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R41.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 41
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R41.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166777 4 rows41 actual41 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R41.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R41.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R41.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R41Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows42 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R42.arithmeticRows.toList
theorem actual42 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166781 4 rows42=true := by decide +kernel
theorem step42 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R42.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 42
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R42.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166781 4 rows42 actual42 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R42.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R42.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R42.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R42Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows43 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R43.arithmeticRows.toList
theorem actual43 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166785 4 rows43=true := by decide +kernel
theorem step43 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R43.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 43
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R43.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166785 4 rows43 actual43 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R43.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R43.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R43.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R43Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B05
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B05.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual37
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual37
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step37
#print axioms ShielddSecurity.MapAssetHashTail736B05.step37
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual38
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual38
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step38
#print axioms ShielddSecurity.MapAssetHashTail736B05.step38
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual39
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual39
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step39
#print axioms ShielddSecurity.MapAssetHashTail736B05.step39
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual40
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual40
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step40
#print axioms ShielddSecurity.MapAssetHashTail736B05.step40
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual41
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual41
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step41
#print axioms ShielddSecurity.MapAssetHashTail736B05.step41
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual42
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual42
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step42
#print axioms ShielddSecurity.MapAssetHashTail736B05.step42
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.actual43
#print axioms ShielddSecurity.MapAssetHashTail736B05.actual43
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B05.step43
#print axioms ShielddSecurity.MapAssetHashTail736B05.step43
