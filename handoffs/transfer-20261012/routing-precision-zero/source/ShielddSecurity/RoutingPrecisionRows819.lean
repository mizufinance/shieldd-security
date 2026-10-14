import ShielddSecurity.RoutingPrecisionBindings816
import ShielddSecurity.RoutingPrecisionCapture818
import ShielddSecurity.VolumeControlBindings803
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionRows819
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingPrecisionAdapter817
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  SemanticCopiesRows801.assignment (RoutingPrecisionSeed811.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

def precision (w : TransferSem.Witness) (slot : Nat) : Nat :=
  if slot<33 then w.routing.regulatedPrecision else w.routing.unregulatedPrecision

theorem column_member (column : Nat) (lower : 19455≤column) (upper : column<19589) :
    column∈RoutingPrecisionLayout808.columns := by
  apply List.mem_range'.mpr
  exact ⟨column-19455,by omega,by omega⟩

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem frame (column : Nat) (member : column∈RoutingPrecisionLayout808.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      RoutingPrecisionSeed811.seed original w column := by
  unfold assignment
  exact RoutingPrecisionBindings816.seeded_frame original u c w legal rkInitial authInitial initial
    senderInitial receiverInitial column member

theorem input (slot : Fin 66) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (inputColumn slot.val)=
      (precision w slot.val:F) := by
  rw [frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial _
    (column_member _ (by unfold inputColumn;split <;> omega) (by unfold inputColumn;split <;> omega))]
  by_cases before : slot.val<33
  · simpa only [inputColumn,precision,if_pos before] using RoutingPrecisionSeed811.regulated original w
  · simpa only [inputColumn,precision,if_neg before] using RoutingPrecisionSeed811.unregulated original w

theorem flag (slot : Fin 66) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (flagColumn slot.val)=
      FieldZeroSeed125.flag ((precision w slot.val:F)-((slot.val%33:Nat):F)) := by
  have bound := slot.isLt
  rw [frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial _
    (column_member _ (by unfold flagColumn;omega) (by unfold flagColumn;omega))]
  by_cases before : slot.val<33
  · have modulo : slot.val%33=slot.val := Nat.mod_eq_of_lt before
    simpa only [flagColumn,precision,if_pos before,RoutingPrecisionSeed811.start,RoutingPrecisionSeed811.precision,
      Bool.false_eq_true,if_false,modulo] using RoutingPrecisionSeed811.flag original w false ⟨slot.val,before⟩
  · have second : slot.val-33<33 := by omega
    have modulo : slot.val%33=slot.val-33 := by omega
    have column : flagColumn slot.val=RoutingPrecisionSeed811.start true+2*(slot.val-33) := by unfold flagColumn RoutingPrecisionSeed811.start;simp only [if_true];omega
    rw [column]
    simpa only [precision,if_neg before,RoutingPrecisionSeed811.precision,if_true,modulo] using
      RoutingPrecisionSeed811.flag original w true ⟨slot.val-33,second⟩

theorem inverse (slot : Fin 66) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (hintColumn slot.val)=
      ((precision w slot.val:F)-((slot.val%33:Nat):F))⁻¹ := by
  have bound := slot.isLt
  rw [frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial _
    (column_member _ (by unfold hintColumn flagColumn;omega) (by unfold hintColumn flagColumn;omega))]
  by_cases before : slot.val<33
  · have modulo : slot.val%33=slot.val := Nat.mod_eq_of_lt before
    simpa only [hintColumn,flagColumn,precision,if_pos before,RoutingPrecisionSeed811.start,RoutingPrecisionSeed811.precision,
      Bool.false_eq_true,if_false,modulo] using RoutingPrecisionSeed811.inverse original w false ⟨slot.val,before⟩
  · have second : slot.val-33<33 := by omega
    have modulo : slot.val%33=slot.val-33 := by omega
    have column : hintColumn slot.val=RoutingPrecisionSeed811.start true+2*(slot.val-33)+1 := by unfold hintColumn flagColumn RoutingPrecisionSeed811.start;simp only [if_true];omega
    rw [column]
    simpa only [precision,if_neg before,RoutingPrecisionSeed811.precision,if_true,modulo] using
      RoutingPrecisionSeed811.inverse original w true ⟨slot.val-33,second⟩

def Rows (rho : Nat → F) : Prop := ∀ slot : Fin 66,RoutingPrecisionAdapter817.Rows rho slot.val

theorem rows : Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  let rho := assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have one := VolumeControlBindings803.copied (RoutingPrecisionSeed811.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := VolumeControlBindings803.arithmetic (RoutingPrecisionSeed811.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
  have one : rho copy=1 := by simpa only [rho,assignment] using one
  have arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 := by simpa only [rho,assignment] using arithmetic
  intro slot
  have equations := RoutingPrecisionCapture818.equations rho one arithmetic slot
  have input := input original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
  have flag := flag original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
  have inverse := inverse original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
  change rho (inputColumn slot.val)=(precision w slot.val:F) at input
  change rho (flagColumn slot.val)=FieldZeroSeed125.flag ((precision w slot.val:F)-((slot.val%33:Nat):F)) at flag
  change rho (hintColumn slot.val)=((precision w slot.val:F)-((slot.val%33:Nat):F))⁻¹ at inverse
  rw [input,flag,inverse] at equations
  apply RoutingPrecisionCapture818.rows rho one slot
  · rw [flag]
    exact equations.1.trans (FieldZeroSeed125.inverse _)
  · exact equations.2.trans (FieldZeroSeed125.annihilated _)
end ShielddSecurity.RoutingPrecisionRows819

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.column_member
#print axioms ShielddSecurity.RoutingPrecisionRows819.column_member

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.frame
#print axioms ShielddSecurity.RoutingPrecisionRows819.frame

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.input
#print axioms ShielddSecurity.RoutingPrecisionRows819.input

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.flag
#print axioms ShielddSecurity.RoutingPrecisionRows819.flag

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.inverse
#print axioms ShielddSecurity.RoutingPrecisionRows819.inverse

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.Rows
#print axioms ShielddSecurity.RoutingPrecisionRows819.Rows

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionRows819.rows
#print axioms ShielddSecurity.RoutingPrecisionRows819.rows
