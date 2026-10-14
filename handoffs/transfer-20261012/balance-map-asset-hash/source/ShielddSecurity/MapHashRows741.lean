import ShielddSecurity.MapAssetHashMeaning740
import ShielddSecurity.MapRootRows708
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapHashRows741
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt

noncomputable def initialRows : List Row := [⟨[(189645,(p:Int)-1),(copy,1)],[]⟩]
theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+20995) 1 initialRows=true := by decide +kernel

theorem initial_rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 189645=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20995+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+20995) 1 initialRows captured rho).mp
  intro row member
  simp only [initialRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(189645,(p:Int)-1),(copy,1)]*eval rho [(189645,(p:Int)-1),(copy,1)]=eval rho []
  have shape : canonical p [(189645,(p:Int)-1),(copy,1)]=canonical p [(189645,-1),(copy,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]

theorem selected_row (rho : Nat → F)
    (rows : SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20997+i)) 2) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20998+i)) 1 := by
  unfold SatisfiesAt at rows ⊢
  intro index before row found
  have equal : index=0 := by omega
  subst index
  exact rows 1 (by decide) row found

noncomputable def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20995+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20998+i)) 1

theorem completed_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original (MapAssetHashMeaning740.input c w) c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  let u := MapAssetHashMeaning740.input c w
  have values := MapAssignmentValues720.values original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have meaning := MapAssetHashMeaning740.meaning original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have inverse := MapFirstCubic707.initial_inverse _ u values.copied meaning values.initialInverse arithmetic
  have qr := (MapAssignmentValues720.stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 20936
    (by change 20936∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.qr u)
  have roots := MapRootRows708.rows _ u values.copied meaning values.initialInverse values.flag qr values.selected arithmetic
  exact ⟨initial_rows _ values.copied inverse,selected_row _ roots⟩
end ShielddSecurity.MapHashRows741

set_option pp.all true in
#check @ShielddSecurity.MapHashRows741.captured
#print axioms ShielddSecurity.MapHashRows741.captured

set_option pp.all true in
#check @ShielddSecurity.MapHashRows741.initial_rows
#print axioms ShielddSecurity.MapHashRows741.initial_rows

set_option pp.all true in
#check @ShielddSecurity.MapHashRows741.selected_row
#print axioms ShielddSecurity.MapHashRows741.selected_row

set_option pp.all true in
#check @ShielddSecurity.MapHashRows741.Rows
#print axioms ShielddSecurity.MapHashRows741.Rows

set_option pp.all true in
#check @ShielddSecurity.MapHashRows741.completed_rows
#print axioms ShielddSecurity.MapHashRows741.completed_rows
