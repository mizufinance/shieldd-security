import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof00
import ShielddSecurity.TransferPoseidonCall04Proof01
import ShielddSecurity.TransferPoseidonCall04Proof02
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B00
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows2 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R02.arithmeticRows.toList
 theorem actual2 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96396 24 rows2=true := by decide +kernel
 theorem step2 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R02.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 2
       (fun i => eval rho (linear ren (TransferPoseidonCall04R02.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96396 24 rows2 actual2 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R02.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R02.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R02.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R02Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows3 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R03.arithmeticRows.toList
 theorem actual3 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96420 24 rows3=true := by decide +kernel
 theorem step3 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R03.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 3
       (fun i => eval rho (linear ren (TransferPoseidonCall04R03.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96420 24 rows3 actual3 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R03.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R03.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R03.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R03Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows4 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R04.arithmeticRows.toList
 theorem actual4 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96444 4 rows4=true := by decide +kernel
 theorem step4 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R04.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 4
       (fun i => eval rho (linear ren (TransferPoseidonCall04R04.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96444 4 rows4 actual4 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R04.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R04.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R04.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R04Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C148B00
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.actual2
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.actual2
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.step2
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.step2
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.actual3
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.actual3
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.step3
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.step3
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.actual4
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.actual4
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B00.step4
#print axioms ShielddSecurity.VolumePathHashTail928C148B00.step4
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B01
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows5 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R05.arithmeticRows.toList
 theorem actual5 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96448 4 rows5=true := by decide +kernel
 theorem step5 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R05.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 5
       (fun i => eval rho (linear ren (TransferPoseidonCall04R05.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96448 4 rows5 actual5 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R05.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R05.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R05.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R05Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows6 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R06.arithmeticRows.toList
 theorem actual6 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96452 4 rows6=true := by decide +kernel
 theorem step6 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R06.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 6
       (fun i => eval rho (linear ren (TransferPoseidonCall04R06.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96452 4 rows6 actual6 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R06.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R06.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R06.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R06Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows7 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R07.arithmeticRows.toList
 theorem actual7 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96456 4 rows7=true := by decide +kernel
 theorem step7 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R07.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 7
       (fun i => eval rho (linear ren (TransferPoseidonCall04R07.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96456 4 rows7 actual7 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R07.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R07.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R07.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R07Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C148B01
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.actual5
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.actual5
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.step5
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.step5
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.actual6
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.actual6
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.step6
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.step6
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.actual7
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.actual7
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B01.step7
#print axioms ShielddSecurity.VolumePathHashTail928C148B01.step7
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B02
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows8 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R08.arithmeticRows.toList
 theorem actual8 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96460 4 rows8=true := by decide +kernel
 theorem step8 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R08.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 8
       (fun i => eval rho (linear ren (TransferPoseidonCall04R08.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96460 4 rows8 actual8 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R08.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R08.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R08.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R08Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows9 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R09.arithmeticRows.toList
 theorem actual9 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96464 4 rows9=true := by decide +kernel
 theorem step9 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R09.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 9
       (fun i => eval rho (linear ren (TransferPoseidonCall04R09.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96464 4 rows9 actual9 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R09.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R09.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R09.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R09Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows10 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R10.arithmeticRows.toList
 theorem actual10 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96468 4 rows10=true := by decide +kernel
 theorem step10 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R10.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 10
       (fun i => eval rho (linear ren (TransferPoseidonCall04R10.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96468 4 rows10 actual10 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R10.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R10.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R10.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R10Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C148B02
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.actual8
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.actual8
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.step8
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.step8
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.actual9
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.actual9
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.step9
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.step9
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.actual10
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.actual10
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B02.step10
#print axioms ShielddSecurity.VolumePathHashTail928C148B02.step10
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B03
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows11 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R11.arithmeticRows.toList
 theorem actual11 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96472 4 rows11=true := by decide +kernel
 theorem step11 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R11.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 11
       (fun i => eval rho (linear ren (TransferPoseidonCall04R11.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96472 4 rows11 actual11 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R11.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R11.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R11.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R11Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows12 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R12.arithmeticRows.toList
 theorem actual12 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96476 4 rows12=true := by decide +kernel
 theorem step12 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R12.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 12
       (fun i => eval rho (linear ren (TransferPoseidonCall04R12.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96476 4 rows12 actual12 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R12.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R12.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R12.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R12Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows13 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R13.arithmeticRows.toList
 theorem actual13 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96480 4 rows13=true := by decide +kernel
 theorem step13 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R13.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 13
       (fun i => eval rho (linear ren (TransferPoseidonCall04R13.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96480 4 rows13 actual13 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R13.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R13.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R13.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R13Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C148B03
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.actual11
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.actual11
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.step11
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.step11
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.actual12
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.actual12
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.step12
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.step12
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.actual13
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.actual13
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B03.step13
#print axioms ShielddSecurity.VolumePathHashTail928C148B03.step13
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B04
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows14 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R14.arithmeticRows.toList
 theorem actual14 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96484 4 rows14=true := by decide +kernel
 theorem step14 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R14.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 14
       (fun i => eval rho (linear ren (TransferPoseidonCall04R14.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96484 4 rows14 actual14 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R14.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R14.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R14.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R14Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows15 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R15.arithmeticRows.toList
 theorem actual15 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96488 4 rows15=true := by decide +kernel
 theorem step15 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R15.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 15
       (fun i => eval rho (linear ren (TransferPoseidonCall04R15.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96488 4 rows15 actual15 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R15.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R15.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R15.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R15Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows16 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R16.arithmeticRows.toList
 theorem actual16 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96492 4 rows16=true := by decide +kernel
 theorem step16 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R16.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 16
       (fun i => eval rho (linear ren (TransferPoseidonCall04R16.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96492 4 rows16 actual16 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R16.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R16.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R16.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R16Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C148B04
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.actual14
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.actual14
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.step14
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.step14
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.actual15
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.actual15
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.step15
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.step15
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.actual16
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.actual16
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B04.step16
#print axioms ShielddSecurity.VolumePathHashTail928C148B04.step16
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B05
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows17 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R17.arithmeticRows.toList
 theorem actual17 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96496 4 rows17=true := by decide +kernel
 theorem step17 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R17.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 17
       (fun i => eval rho (linear ren (TransferPoseidonCall04R17.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96496 4 rows17 actual17 (by decide) rho arithmetic
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
 theorem actual18 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96500 4 rows18=true := by decide +kernel
 theorem step18 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R18.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 18
       (fun i => eval rho (linear ren (TransferPoseidonCall04R18.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96500 4 rows18 actual18 (by decide) rho arithmetic
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
 theorem actual19 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96504 4 rows19=true := by decide +kernel
 theorem step19 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R19.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 19
       (fun i => eval rho (linear ren (TransferPoseidonCall04R19.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96504 4 rows19 actual19 (by decide) rho arithmetic
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
 end ShielddSecurity.VolumePathHashTail928C148B05
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.actual17
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.actual17
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.step17
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.step17
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.actual18
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.actual18
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.step18
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.step18
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.actual19
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.actual19
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B05.step19
#print axioms ShielddSecurity.VolumePathHashTail928C148B05.step19
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C148B06
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 96034
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows20 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R20.arithmeticRows.toList
 theorem actual20 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96508 4 rows20=true := by decide +kernel
 theorem step20 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R20.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 20
       (fun i => eval rho (linear ren (TransferPoseidonCall04R20.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96508 4 rows20 actual20 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R20.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R20.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R20.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R20Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows21 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R21.arithmeticRows.toList
 theorem actual21 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96512 4 rows21=true := by decide +kernel
 theorem step21 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R21.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 21
       (fun i => eval rho (linear ren (TransferPoseidonCall04R21.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96512 4 rows21 actual21 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R21.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R21.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R21.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R21Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows22 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R22.arithmeticRows.toList
 theorem actual22 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 96516 4 rows22=true := by decide +kernel
 theorem step22 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R22.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 22
       (fun i => eval rho (linear ren (TransferPoseidonCall04R22.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 96516 4 rows22 actual22 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R22.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R22.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R22.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R22Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C148B06
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.actual20
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.actual20
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.step20
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.step20
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.actual21
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.actual21
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.step21
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.step21
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.actual22
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.actual22
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C148B06.step22
#print axioms ShielddSecurity.VolumePathHashTail928C148B06.step22
