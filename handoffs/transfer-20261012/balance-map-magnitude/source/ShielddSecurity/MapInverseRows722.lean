import ShielddSecurity.MapAssignmentValues720
import ShielddSecurity.BalanceBlindingCanonical691
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapInverseRows722
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model

noncomputable def assertionRows : List Row :=
  [⟨[(21193,1),(190169,1),(copy,(p:Int)-1)],[]⟩,
   ⟨[(190171,(p:Int)-1)],[]⟩,⟨[(190173,(p:Int)-1)],[]⟩,
   ⟨[(190189,(p:Int)-1),(copy,1)],[]⟩,
   ⟨[(190209,(p:Int)-1),(copy,1)],[]⟩,
   ⟨[(190229,(p:Int)-1),(copy,1)],[]⟩]

theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+21259) 6 assertionRows=true := by decide +kernel

theorem negative_one : (((p:Int)-1):F)= -1 := by
  change (Scalar.modulus:F)-1= -1
  rw [ZMod.natCast_self,zero_sub]

private theorem linear_satisfied (rho : Nat → F) (actual normal : Linear)
    (shape : canonical p actual=canonical p normal) (zero : eval rho normal=0) :
    Square (eval rho actual) (eval rho []) := by
  rw [canonical_equal rho actual normal shape,zero]
  rfl

theorem rows (rho : Nat → F) (u : F) (values : MapCofactorJoin714.Values rho u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+21259+i)) 6 := by
  have inverse := MapRational710.inverse_values rho u values.toValues arithmetic
  have doubles := MapCofactorJoin714.doublings rho u values arithmetic
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+21259) 6 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  · apply linear_satisfied rho _ [(21193,1),(190169,1),(copy,-1)] (by decide +kernel)
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,values.copied,
      values.zero,inverse.1,inverse.2.1,inverse.2.2,doubles.1,doubles.2.1,doubles.2.2.1]
    ring
  · apply linear_satisfied rho _ [(190171,-1)] (by decide +kernel)
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,values.copied,
      values.zero,inverse.1,inverse.2.1,inverse.2.2,doubles.1,doubles.2.1,doubles.2.2.1]
    ring
  · apply linear_satisfied rho _ [(190173,-1)] (by decide +kernel)
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,values.copied,
      values.zero,inverse.1,inverse.2.1,inverse.2.2,doubles.1,doubles.2.1,doubles.2.2.1]
    ring
  · apply linear_satisfied rho _ [(190189,-1),(copy,1)] (by decide +kernel)
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,values.copied,
      values.zero,inverse.1,inverse.2.1,inverse.2.2,doubles.1,doubles.2.1,doubles.2.2.1]
    ring
  · apply linear_satisfied rho _ [(190209,-1),(copy,1)] (by decide +kernel)
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,values.copied,
      values.zero,inverse.1,inverse.2.1,inverse.2.2,doubles.1,doubles.2.1,doubles.2.2.1]
    ring
  · apply linear_satisfied rho _ [(190229,-1),(copy,1)] (by decide +kernel)
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,values.copied,
      values.zero,inverse.1,inverse.2.1,inverse.2.2,doubles.1,doubles.2.1,doubles.2.2.1]
    ring


theorem zero (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
  unfold MapAssignmentValues720.assignment BalanceCombined696.assignment
  exact BalanceBlindingCanonical691.zero _ c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem completed_rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+21259+i)) 6 :=
  rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) u
    (MapAssignmentValues720.values original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
end ShielddSecurity.MapInverseRows722

set_option pp.all true in
#check @ShielddSecurity.MapInverseRows722.captured
#print axioms ShielddSecurity.MapInverseRows722.captured

set_option pp.all true in
#check @ShielddSecurity.MapInverseRows722.negative_one
#print axioms ShielddSecurity.MapInverseRows722.negative_one

set_option pp.all true in
#check @ShielddSecurity.MapInverseRows722.rows
#print axioms ShielddSecurity.MapInverseRows722.rows

set_option pp.all true in
#check @ShielddSecurity.MapInverseRows722.zero
#print axioms ShielddSecurity.MapInverseRows722.zero

set_option pp.all true in
#check @ShielddSecurity.MapInverseRows722.completed_rows
#print axioms ShielddSecurity.MapInverseRows722.completed_rows
