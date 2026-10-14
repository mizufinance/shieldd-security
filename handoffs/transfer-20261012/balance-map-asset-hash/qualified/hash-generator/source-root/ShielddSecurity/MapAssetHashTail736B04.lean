/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof03
import ShielddSecurity.TransferPoseidonWidth3Call08Proof04
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B04
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows30 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R30.arithmeticRows.toList
theorem actual30 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166733 4 rows30=true := by decide +kernel
theorem step30 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R30.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 30
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R30.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166733 4 rows30 actual30 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R30.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R30.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R30.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R30Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows31 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R31.arithmeticRows.toList
theorem actual31 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166737 4 rows31=true := by decide +kernel
theorem step31 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R31.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 31
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R31.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166737 4 rows31 actual31 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R31.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R31.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R31.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R31Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows32 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R32.arithmeticRows.toList
theorem actual32 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166741 4 rows32=true := by decide +kernel
theorem step32 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R32.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 32
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R32.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166741 4 rows32 actual32 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R32.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R32.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R32.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R32Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows33 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R33.arithmeticRows.toList
theorem actual33 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166745 4 rows33=true := by decide +kernel
theorem step33 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R33.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 33
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R33.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166745 4 rows33 actual33 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R33.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R33.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R33.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R33Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows34 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R34.arithmeticRows.toList
theorem actual34 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166749 4 rows34=true := by decide +kernel
theorem step34 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R34.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 34
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R34.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166749 4 rows34 actual34 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R34.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R34.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R34.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R34Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows35 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R35.arithmeticRows.toList
theorem actual35 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166753 4 rows35=true := by decide +kernel
theorem step35 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R35.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 35
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R35.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166753 4 rows35 actual35 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R35.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R35.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R35.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R35Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows36 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R36.arithmeticRows.toList
theorem actual36 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166757 4 rows36=true := by decide +kernel
theorem step36 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R36.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 36
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R36.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166757 4 rows36 actual36 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R36.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R36.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R36.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R36Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B04
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B04.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual30
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual30
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step30
#print axioms ShielddSecurity.MapAssetHashTail736B04.step30
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual31
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual31
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step31
#print axioms ShielddSecurity.MapAssetHashTail736B04.step31
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual32
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual32
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step32
#print axioms ShielddSecurity.MapAssetHashTail736B04.step32
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual33
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual33
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step33
#print axioms ShielddSecurity.MapAssetHashTail736B04.step33
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual34
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual34
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step34
#print axioms ShielddSecurity.MapAssetHashTail736B04.step34
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual35
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual35
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step35
#print axioms ShielddSecurity.MapAssetHashTail736B04.step35
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.actual36
#print axioms ShielddSecurity.MapAssetHashTail736B04.actual36
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B04.step36
#print axioms ShielddSecurity.MapAssetHashTail736B04.step36
