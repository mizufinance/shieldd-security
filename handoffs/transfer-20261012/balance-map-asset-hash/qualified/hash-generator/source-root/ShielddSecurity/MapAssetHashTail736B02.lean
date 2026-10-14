/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonWidth3Call08Proof02
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashTail736B02
open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
open CapturedInitial73419Generic01 (p copy)
noncomputable def ren := CompilerWindowRenaming05.swap 24732 312 164599
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
noncomputable def rows16 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R16.arithmeticRows.toList
theorem actual16 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166677 4 rows16=true := by decide +kernel
theorem step16 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R16.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 16
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R16.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166677 4 rows16 actual16 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R16.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R16.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R16.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R16Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows17 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R17.arithmeticRows.toList
theorem actual17 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166681 4 rows17=true := by decide +kernel
theorem step17 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R17.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 17
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R17.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166681 4 rows17 actual17 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R17.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R17.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R17.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R17Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows18 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R18.arithmeticRows.toList
theorem actual18 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166685 4 rows18=true := by decide +kernel
theorem step18 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R18.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 18
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R18.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166685 4 rows18 actual18 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R18.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R18.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R18.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R18Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows19 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R19.arithmeticRows.toList
theorem actual19 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166689 4 rows19=true := by decide +kernel
theorem step19 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R19.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 19
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R19.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166689 4 rows19 actual19 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R19.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R19.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R19.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R19Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows20 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R20.arithmeticRows.toList
theorem actual20 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166693 4 rows20=true := by decide +kernel
theorem step20 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R20.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 20
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R20.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166693 4 rows20 actual20 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R20.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R20.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R20.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R20Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows21 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R21.arithmeticRows.toList
theorem actual21 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166697 4 rows21=true := by decide +kernel
theorem step21 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R21.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 21
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R21.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166697 4 rows21 actual21 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R21.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R21.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R21.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R21Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
noncomputable def rows22 := CompilerColumnRenaming05.rows ren TransferPoseidonWidth3Call08R22.arithmeticRows.toList
theorem actual22 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 166701 4 rows22=true := by decide +kernel
theorem step22 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R22.after i)))=Poseidon.round
      (Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters) 22
      (fun i => eval rho (linear ren (TransferPoseidonWidth3Call08R22.before i))) := by
  have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 166701 4 rows22 actual22 (by decide) rho arithmetic
  have source := (satisfies_rows ren rho TransferPoseidonWidth3Call08R22.arithmeticRows.toList).mp target
  have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
    (by simpa only [fixed.1,fixed.2] using linked)
  have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonWidth3Call08R22.originalRows.toList := by
    change Satisfies (fun c => rho (ren c)) (TransferPoseidonWidth3Call08R22.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
    intro row member
    rcases List.mem_append.mp member with left|right
    · exact source row left
    · exact copied row right
  have result := TransferPoseidonWidth3Call08R22Proof.arbitrary_round_sound (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
  simpa only [eval_linear] using result
end ShielddSecurity.MapAssetHashTail736B02
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.fixed
#print axioms ShielddSecurity.MapAssetHashTail736B02.fixed
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual16
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual16
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step16
#print axioms ShielddSecurity.MapAssetHashTail736B02.step16
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual17
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual17
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step17
#print axioms ShielddSecurity.MapAssetHashTail736B02.step17
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual18
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual18
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step18
#print axioms ShielddSecurity.MapAssetHashTail736B02.step18
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual19
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual19
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step19
#print axioms ShielddSecurity.MapAssetHashTail736B02.step19
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual20
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual20
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step20
#print axioms ShielddSecurity.MapAssetHashTail736B02.step20
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual21
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual21
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step21
#print axioms ShielddSecurity.MapAssetHashTail736B02.step21
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.actual22
#print axioms ShielddSecurity.MapAssetHashTail736B02.actual22
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashTail736B02.step22
#print axioms ShielddSecurity.MapAssetHashTail736B02.step22
