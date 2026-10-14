import ShielddSecurity.MapAssetDomain743
import ShielddSecurity.AuthorizationAddRows511
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalDomain751
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model

def magnitude (u : F) (w : TransferSem.Witness) : Group.Point F :=
  model.coordinates (RemainingWordSeed369.magnitude w • BalanceMapPoint701.represented u)
def left (u : F) (w : TransferSem.Witness) : Group.Point F :=
  if BalanceSignBindings652.negative w then ⟨-(magnitude u w).x,(magnitude u w).y⟩ else magnitude u w
def right (w : TransferSem.Witness) : Group.Point F :=
  model.coordinates (w.blinding • BalanceBlindingDomain670.represented)
def delta (u : F) (w : TransferSem.Witness) : F :=
  Group.delta (CapturedFirstSubgroup81.d:F) (left u w) (right w)
def denominator (u : F) (w : TransferSem.Witness) : F := (1+delta u w)*(1-delta u w)
def seed (original : Nat → F) (u : F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=22736 then (denominator u w)⁻¹ else original column

theorem left_onCurve (u : F) (w : TransferSem.Witness) :
    Group.OnCurve (CapturedFirstSubgroup81.d:F) (left u w) := by
  have h : Group.OnCurve (CapturedFirstSubgroup81.d:F) (magnitude u w) := model.onCurve _
  unfold left
  split
  · simpa only [Group.OnCurve,neg_mul_neg,mul_neg,neg_mul,neg_neg] using h
  · exact h

theorem denominator_nonzero (u : F) (w : TransferSem.Witness) : denominator u w≠0 := by
  have nonzero := Group.denominators_nonzero (CapturedFirstSubgroup81.d:F) imaginary
    (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
    (left u w) (right w) (left_onCurve u w) (model.onCurve _)
  exact mul_ne_zero nonzero.1 nonzero.2

theorem selected (original : Nat → F) (u : F) (w : TransferSem.Witness) :
    seed original u w 22736=(denominator u w)⁻¹ := by simp only [seed,if_pos rfl,if_true]

theorem coordinates (u : F) (w : TransferSem.Witness) :
    Group.Point.mk
      (Group.cross (left u w) (right w)*(1-delta u w)*(denominator u w)⁻¹)
      (Group.diagonal (left u w) (right w)*(1+delta u w)*(denominator u w)⁻¹)=
    Group.affineAdd (CapturedFirstSubgroup81.d:F) (left u w) (right w) :=
  AuthorizationAddRows511.coordinates _ _ _ (denominator_nonzero u w)
end ShielddSecurity.BalanceFinalDomain751

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalDomain751.left_onCurve
#print axioms ShielddSecurity.BalanceFinalDomain751.left_onCurve

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalDomain751.denominator_nonzero
#print axioms ShielddSecurity.BalanceFinalDomain751.denominator_nonzero

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalDomain751.selected
#print axioms ShielddSecurity.BalanceFinalDomain751.selected

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalDomain751.coordinates
#print axioms ShielddSecurity.BalanceFinalDomain751.coordinates
