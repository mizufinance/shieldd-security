/- Generated from maintained volume output-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof04
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumeOutputHashTail915C152B11
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 97674
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows35 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R35.arithmeticRows.toList
 theorem actual35 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98208 4 rows35=true := by decide +kernel
 theorem step35 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R35.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 35
       (fun i => eval rho (linear ren (TransferPoseidonCall04R35.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98208 4 rows35 actual35 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R35.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R35.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R35.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R35Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows36 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R36.arithmeticRows.toList
 theorem actual36 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98212 4 rows36=true := by decide +kernel
 theorem step36 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R36.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 36
       (fun i => eval rho (linear ren (TransferPoseidonCall04R36.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98212 4 rows36 actual36 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R36.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R36.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R36.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R36Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows37 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R37.arithmeticRows.toList
 theorem actual37 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98216 4 rows37=true := by decide +kernel
 theorem step37 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R37.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 37
       (fun i => eval rho (linear ren (TransferPoseidonCall04R37.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98216 4 rows37 actual37 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R37.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R37.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R37.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R37Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumeOutputHashTail915C152B11
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.fixed
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.actual35
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.actual35
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.step35
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.step35
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.actual36
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.actual36
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.step36
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.step36
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.actual37
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.actual37
set_option pp.all true in
#check @ShielddSecurity.VolumeOutputHashTail915C152B11.step37
#print axioms ShielddSecurity.VolumeOutputHashTail915C152B11.step37
