import ShielddSecurity.TierFrame615
import ShielddSecurity.AuthorizationTraceLocal453
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierTrace616
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierLayout613
open AuthorizationTraceSeed451 (hintPoint coordinate)
attribute [local irreducible] hintPoint model

def one (original : Nat → F) (base : curve.Point) (scalar start column : Nat) : F :=
  if start≤column ∧ column<start+756 then
    coordinate (hintPoint base scalar ((column-start)/2)) ((column-start)%2)
  else original column

theorem one_outside (original : Nat → F) (base : curve.Point) (scalar start column : Nat)
    (separate : column<start ∨ start+756≤column) : one original base scalar start column=original column := by
  simp only [one,if_neg (show ¬(start≤column ∧ column<start+756) by omega)]

theorem one_limb (original : Nat → F) (base : curve.Point) (scalar start index limb : Nat)
    (before : index<378) (small : limb<2) :
    one original base scalar start (start+2*index+limb)=coordinate (hintPoint base scalar index) limb := by
  have bounds : start≤start+2*index+limb ∧ start+2*index+limb<start+756 := by omega
  have quotient : (start+2*index+limb-start)/2=index := by omega
  have remainder : (start+2*index+limb-start)%2=limb := by omega
  simp only [one,if_pos bounds,quotient,remainder]

def seed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) : Nat → F :=
  one (one (one (one (one (original) (TierGroupDomain612.represented c w ⟨4,by decide⟩ legal) (scalar w ⟨4,by decide⟩) 16659) (TierGroupDomain612.represented c w ⟨3,by decide⟩ legal) (scalar w ⟨3,by decide⟩) 15397) (TierGroupDomain612.represented c w ⟨2,by decide⟩ legal) (scalar w ⟨2,by decide⟩) 14135) (TierGroupDomain612.represented c w ⟨1,by decide⟩ legal) (scalar w ⟨1,by decide⟩) 12873) (TierGroupDomain612.represented c w ⟨0,by decide⟩ legal) (scalar w ⟨0,by decide⟩) 12117

theorem limb0 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (index limb : Nat)
    (before : index<378) (small : limb<2) :
    seed original c w legal (12117+2*index+limb)=
      coordinate (hintPoint (TierGroupDomain612.represented c w ⟨0,by decide⟩ legal) (scalar w ⟨0,by decide⟩) index) limb := by
  unfold seed
  exact one_limb _ _ _ _ index limb before small

theorem limb1 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (index limb : Nat)
    (before : index<378) (small : limb<2) :
    seed original c w legal (12873+2*index+limb)=
      coordinate (hintPoint (TierGroupDomain612.represented c w ⟨1,by decide⟩ legal) (scalar w ⟨1,by decide⟩) index) limb := by
  unfold seed
  rw [one_outside _ _ _ 12117 _ (Or.inr (by omega))]
  exact one_limb _ _ _ _ index limb before small

theorem limb2 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (index limb : Nat)
    (before : index<378) (small : limb<2) :
    seed original c w legal (14135+2*index+limb)=
      coordinate (hintPoint (TierGroupDomain612.represented c w ⟨2,by decide⟩ legal) (scalar w ⟨2,by decide⟩) index) limb := by
  unfold seed
  rw [one_outside _ _ _ 12117 _ (Or.inr (by omega))]
  rw [one_outside _ _ _ 12873 _ (Or.inr (by omega))]
  exact one_limb _ _ _ _ index limb before small

theorem limb3 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (index limb : Nat)
    (before : index<378) (small : limb<2) :
    seed original c w legal (15397+2*index+limb)=
      coordinate (hintPoint (TierGroupDomain612.represented c w ⟨3,by decide⟩ legal) (scalar w ⟨3,by decide⟩) index) limb := by
  unfold seed
  rw [one_outside _ _ _ 12117 _ (Or.inr (by omega))]
  rw [one_outside _ _ _ 12873 _ (Or.inr (by omega))]
  rw [one_outside _ _ _ 14135 _ (Or.inr (by omega))]
  exact one_limb _ _ _ _ index limb before small

theorem limb4 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (index limb : Nat)
    (before : index<378) (small : limb<2) :
    seed original c w legal (16659+2*index+limb)=
      coordinate (hintPoint (TierGroupDomain612.represented c w ⟨4,by decide⟩ legal) (scalar w ⟨4,by decide⟩) index) limb := by
  unfold seed
  rw [one_outside _ _ _ 12117 _ (Or.inr (by omega))]
  rw [one_outside _ _ _ 12873 _ (Or.inr (by omega))]
  rw [one_outside _ _ _ 14135 _ (Or.inr (by omega))]
  rw [one_outside _ _ _ 15397 _ (Or.inr (by omega))]
  exact one_limb _ _ _ _ index limb before small

theorem limb (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (family : Fin 5) (index limb : Nat)
    (before : index<378) (small : limb<2) :
    seed original c w legal (pointStart family+2*index+limb)=
      coordinate (hintPoint (TierGroupDomain612.represented c w family legal) (scalar w family) index) limb := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact limb0 original c w legal index limb before small
  · exact limb1 original c w legal index limb before small
  · exact limb2 original c w legal index limb before small
  · exact limb3 original c w legal index limb before small
  · exact limb4 original c w legal index limb before small

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (family : Fin 5) (index : Nat)
    (before : index<378) :
    VariableWindowColumns449.columnPoint (seed original c w legal) (pointStart family+2*index)=
      hintPoint (TierGroupDomain612.represented c w family legal) (scalar w family) index := by
  unfold VariableWindowColumns449.columnPoint
  have x := limb original c w legal family index 0 before (by decide)
  simp only [Nat.add_zero] at x
  rw [x,limb original c w legal family index 1 before (by decide)]
  rfl
end ShielddSecurity.TierTrace616

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.one_outside
#print axioms ShielddSecurity.TierTrace616.one_outside

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.one_limb
#print axioms ShielddSecurity.TierTrace616.one_limb

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.limb0
#print axioms ShielddSecurity.TierTrace616.limb0

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.limb1
#print axioms ShielddSecurity.TierTrace616.limb1

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.limb2
#print axioms ShielddSecurity.TierTrace616.limb2

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.limb3
#print axioms ShielddSecurity.TierTrace616.limb3

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.limb4
#print axioms ShielddSecurity.TierTrace616.limb4

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.limb
#print axioms ShielddSecurity.TierTrace616.limb

set_option pp.all true in
#check @ShielddSecurity.TierTrace616.point
#print axioms ShielddSecurity.TierTrace616.point
