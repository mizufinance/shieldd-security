import ShielddSecurity.AuthorizationPoseidonRowBridge521
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.TransferPoseidonCall04Proof02
import ShielddSecurity.TransferPoseidonCall04Proof03
import ShielddSecurity.TransferPoseidonCall04Proof04
import ShielddSecurity.TransferPoseidonCall04Proof05
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B07
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows23 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R23.arithmeticRows.toList
 theorem actual23 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86768 4 rows23=true := by decide +kernel
 theorem step23 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R23.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 23
       (fun i => eval rho (linear ren (TransferPoseidonCall04R23.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86768 4 rows23 actual23 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R23.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R23.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R23.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R23Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows24 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R24.arithmeticRows.toList
 theorem actual24 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86772 4 rows24=true := by decide +kernel
 theorem step24 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R24.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 24
       (fun i => eval rho (linear ren (TransferPoseidonCall04R24.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86772 4 rows24 actual24 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R24.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R24.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R24.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R24Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows25 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R25.arithmeticRows.toList
 theorem actual25 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86776 4 rows25=true := by decide +kernel
 theorem step25 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R25.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 25
       (fun i => eval rho (linear ren (TransferPoseidonCall04R25.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86776 4 rows25 actual25 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R25.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R25.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R25.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R25Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C125B07
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.actual23
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.actual23
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.step23
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.step23
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.actual24
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.actual24
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.step24
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.step24
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.actual25
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.actual25
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B07.step25
#print axioms ShielddSecurity.VolumePathHashTail928C125B07.step25
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B08
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows26 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R26.arithmeticRows.toList
 theorem actual26 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86780 4 rows26=true := by decide +kernel
 theorem step26 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R26.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 26
       (fun i => eval rho (linear ren (TransferPoseidonCall04R26.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86780 4 rows26 actual26 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R26.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R26.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R26.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R26Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows27 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R27.arithmeticRows.toList
 theorem actual27 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86784 4 rows27=true := by decide +kernel
 theorem step27 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R27.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 27
       (fun i => eval rho (linear ren (TransferPoseidonCall04R27.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86784 4 rows27 actual27 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R27.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R27.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R27.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R27Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows28 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R28.arithmeticRows.toList
 theorem actual28 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86788 4 rows28=true := by decide +kernel
 theorem step28 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R28.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 28
       (fun i => eval rho (linear ren (TransferPoseidonCall04R28.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86788 4 rows28 actual28 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R28.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R28.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R28.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R28Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C125B08
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.actual26
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.actual26
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.step26
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.step26
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.actual27
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.actual27
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.step27
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.step27
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.actual28
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.actual28
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B08.step28
#print axioms ShielddSecurity.VolumePathHashTail928C125B08.step28
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B09
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows29 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R29.arithmeticRows.toList
 theorem actual29 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86792 4 rows29=true := by decide +kernel
 theorem step29 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R29.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 29
       (fun i => eval rho (linear ren (TransferPoseidonCall04R29.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86792 4 rows29 actual29 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R29.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R29.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R29.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R29Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows30 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R30.arithmeticRows.toList
 theorem actual30 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86796 4 rows30=true := by decide +kernel
 theorem step30 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R30.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 30
       (fun i => eval rho (linear ren (TransferPoseidonCall04R30.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86796 4 rows30 actual30 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R30.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R30.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R30.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R30Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows31 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R31.arithmeticRows.toList
 theorem actual31 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86800 4 rows31=true := by decide +kernel
 theorem step31 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R31.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 31
       (fun i => eval rho (linear ren (TransferPoseidonCall04R31.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86800 4 rows31 actual31 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R31.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R31.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R31.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R31Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C125B09
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.actual29
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.actual29
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.step29
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.step29
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.actual30
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.actual30
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.step30
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.step30
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.actual31
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.actual31
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B09.step31
#print axioms ShielddSecurity.VolumePathHashTail928C125B09.step31
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B10
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows32 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R32.arithmeticRows.toList
 theorem actual32 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86804 4 rows32=true := by decide +kernel
 theorem step32 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R32.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 32
       (fun i => eval rho (linear ren (TransferPoseidonCall04R32.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86804 4 rows32 actual32 (by decide) rho arithmetic
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
 theorem actual33 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86808 4 rows33=true := by decide +kernel
 theorem step33 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R33.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 33
       (fun i => eval rho (linear ren (TransferPoseidonCall04R33.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86808 4 rows33 actual33 (by decide) rho arithmetic
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
 theorem actual34 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86812 4 rows34=true := by decide +kernel
 theorem step34 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R34.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 34
       (fun i => eval rho (linear ren (TransferPoseidonCall04R34.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86812 4 rows34 actual34 (by decide) rho arithmetic
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
 end ShielddSecurity.VolumePathHashTail928C125B10
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.actual32
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.actual32
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.step32
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.step32
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.actual33
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.actual33
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.step33
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.step33
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.actual34
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.actual34
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B10.step34
#print axioms ShielddSecurity.VolumePathHashTail928C125B10.step34
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B11
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows35 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R35.arithmeticRows.toList
 theorem actual35 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86816 4 rows35=true := by decide +kernel
 theorem step35 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R35.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 35
       (fun i => eval rho (linear ren (TransferPoseidonCall04R35.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86816 4 rows35 actual35 (by decide) rho arithmetic
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
 theorem actual36 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86820 4 rows36=true := by decide +kernel
 theorem step36 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R36.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 36
       (fun i => eval rho (linear ren (TransferPoseidonCall04R36.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86820 4 rows36 actual36 (by decide) rho arithmetic
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
 theorem actual37 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86824 4 rows37=true := by decide +kernel
 theorem step37 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R37.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 37
       (fun i => eval rho (linear ren (TransferPoseidonCall04R37.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86824 4 rows37 actual37 (by decide) rho arithmetic
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
 end ShielddSecurity.VolumePathHashTail928C125B11
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.actual35
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.actual35
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.step35
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.step35
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.actual36
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.actual36
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.step36
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.step36
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.actual37
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.actual37
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B11.step37
#print axioms ShielddSecurity.VolumePathHashTail928C125B11.step37
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B12
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows38 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R38.arithmeticRows.toList
 theorem actual38 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86828 4 rows38=true := by decide +kernel
 theorem step38 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R38.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 38
       (fun i => eval rho (linear ren (TransferPoseidonCall04R38.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86828 4 rows38 actual38 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R38.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R38.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R38.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R38Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows39 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R39.arithmeticRows.toList
 theorem actual39 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86832 4 rows39=true := by decide +kernel
 theorem step39 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R39.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 39
       (fun i => eval rho (linear ren (TransferPoseidonCall04R39.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86832 4 rows39 actual39 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R39.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R39.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R39.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R39Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows40 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R40.arithmeticRows.toList
 theorem actual40 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86836 4 rows40=true := by decide +kernel
 theorem step40 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R40.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 40
       (fun i => eval rho (linear ren (TransferPoseidonCall04R40.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86836 4 rows40 actual40 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R40.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R40.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R40.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R40Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C125B12
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.actual38
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.actual38
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.step38
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.step38
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.actual39
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.actual39
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.step39
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.step39
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.actual40
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.actual40
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B12.step40
#print axioms ShielddSecurity.VolumePathHashTail928C125B12.step40
/- Generated from maintained volume path-hash generator; edit generator or templates. -/
set_option autoImplicit false
 set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
 noncomputable section
 namespace ShielddSecurity.VolumePathHashTail928C125B13
 open Compiler CompilerAssertionBlock51 CompilerColumnRenaming05
 open CapturedInitial73419Generic01 (p copy)
 def ren := CompilerWindowRenaming05.swap 23076 396 86282
 theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel
 variable {F : Type} [Field F] [CharP F p]
 def rows41 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R41.arithmeticRows.toList
 theorem actual41 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86840 4 rows41=true := by decide +kernel
 theorem step41 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R41.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 41
       (fun i => eval rho (linear ren (TransferPoseidonCall04R41.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86840 4 rows41 actual41 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R41.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R41.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R41.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R41Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows42 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R42.arithmeticRows.toList
 theorem actual42 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86844 4 rows42=true := by decide +kernel
 theorem step42 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R42.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 42
       (fun i => eval rho (linear ren (TransferPoseidonCall04R42.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86844 4 rows42 actual42 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R42.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R42.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R42.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R42Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 def rows43 := CompilerColumnRenaming05.rows ren TransferPoseidonCall04R43.arithmeticRows.toList
 theorem actual43 : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 86848 4 rows43=true := by decide +kernel
 theorem step43 (rho : Nat → F) (one : rho 0=1) (linked : rho copy=rho 0)
     (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
     (fun i => eval rho (linear ren (TransferPoseidonCall04R43.after i)))=Poseidon.round
       (Poseidon.castParameters TransferPoseidonCall04Shared01.parameters) 43
       (fun i => eval rho (linear ren (TransferPoseidonCall04R43.before i))) := by
   have target := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 86848 4 rows43 actual43 (by decide) rho arithmetic
   have source := (satisfies_rows ren rho TransferPoseidonCall04R43.arithmeticRows.toList).mp target
   have copied := AuthorizationPoseidonRowBridge521.copy_satisfied (fun c => rho (ren c))
     (by simpa only [fixed.1,fixed.2] using linked)
   have sat : Satisfies (fun c => rho (ren c)) TransferPoseidonCall04R43.originalRows.toList := by
     change Satisfies (fun c => rho (ren c)) (TransferPoseidonCall04R43.arithmeticRows.toList++[AuthorizationPoseidonRowBridge521.copyRow])
     intro row member
     rcases List.mem_append.mp member with left|right
     · exact source row left
     · exact copied row right
   have result := TransferPoseidonCall04R43Proof.arbitrary_round_sound (fun c => rho (ren c))
     (by simpa only [fixed.1] using one) AuthorizationPoseidonPhase517.four_ne_zero sat
   simpa only [eval_linear] using result
 end ShielddSecurity.VolumePathHashTail928C125B13
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.fixed
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.fixed
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.actual41
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.actual41
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.step41
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.step41
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.actual42
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.actual42
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.step42
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.step42
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.actual43
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.actual43
set_option pp.all true in
#check @ShielddSecurity.VolumePathHashTail928C125B13.step43
#print axioms ShielddSecurity.VolumePathHashTail928C125B13.step43
