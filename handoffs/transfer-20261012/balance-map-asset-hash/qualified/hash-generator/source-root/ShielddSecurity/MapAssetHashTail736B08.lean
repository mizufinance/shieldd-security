/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof07
import ShielddSecurity.TransferPoseidonWidth3Call08Proof08
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B08
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows58 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R58.arithmeticRows.toList
theorem actual58 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166845 4 rows58=true := by decide +kernel
theorem step58 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R58.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 58
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R58.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166845 4 rows58 actual58 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R58.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R58.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R58.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R58Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows59 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R59.arithmeticRows.toList
theorem actual59 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166849 4 rows59=true := by decide +kernel
theorem step59 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R59.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 59
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R59.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166849 4 rows59 actual59 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R59.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R59.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R59.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R59Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows60 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R60.arithmeticRows.toList
theorem actual60 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166853 4 rows60=true := by decide +kernel
theorem step60 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R60.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 60
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R60.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166853 4 rows60 actual60 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R60.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R60.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R60.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R60Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows61 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R61.arithmeticRows.toList
theorem actual61 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166857 12 rows61=true := by decide +kernel
theorem step61 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R61.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 61
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R61.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166857 12 rows61 actual61 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R61.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R61.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R61.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R61Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows62 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R62.arithmeticRows.toList
theorem actual62 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166869 12 rows62=true := by decide +kernel
theorem step62 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R62.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 62
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R62.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166869 12 rows62 actual62 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R62.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R62.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R62.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R62Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows63 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R63.arithmeticRows.toList
theorem actual63 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166881 12 rows63=true := by decide +kernel
theorem step63 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R63.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 63
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R63.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166881 12 rows63 actual63 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R63.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R63.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R63.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R63Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows64 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R64.arithmeticRows.toList
theorem actual64 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166893 12 rows64=true := by decide +kernel
theorem step64 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R64.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 64
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R64.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166893 12 rows64 actual64 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R64.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R64.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R64.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R64Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B08
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B08.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual58
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual58
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step58
#print axioms ShielddSecurity.MapAssetHashTail736B08.step58
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual59
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual59
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step59
#print axioms ShielddSecurity.MapAssetHashTail736B08.step59
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual60
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual60
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step60
#print axioms ShielddSecurity.MapAssetHashTail736B08.step60
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual61
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual61
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step61
#print axioms ShielddSecurity.MapAssetHashTail736B08.step61
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual62
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual62
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step62
#print axioms ShielddSecurity.MapAssetHashTail736B08.step62
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual63
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual63
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step63
#print axioms ShielddSecurity.MapAssetHashTail736B08.step63
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.actual64
#print axioms ShielddSecurity.MapAssetHashTail736B08.actual64
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B08.step64
#print axioms ShielddSecurity.MapAssetHashTail736B08.step64
