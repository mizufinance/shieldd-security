import ShielddSecurity.FixedFamilyFrame547
import ShielddSecurity.AuthorizationFixedLocal493
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilySeed549
open ConcreteJubjubField01 TransferSem FixedFamilyLayout545
open AuthorizationFixedSeed487 (window)
attribute [local irreducible] window ConcreteRegistrySharedEncoding294.model

def one (original : Nat → F) (scalar start column : Nat) : F :=
  if start≤column ∧ column<start+252 then
    let output := (window scalar ((column-start)/2)).output
    if (column-start)%2=0 then output.x else output.y
  else original column

theorem one_outside (original : Nat → F) (scalar start column : Nat)
    (separate : column<start ∨ start+252≤column) : one original scalar start column=original column := by
  simp only [one,if_neg (show ¬(start≤column ∧ column<start+252) by omega)]
theorem one_limb (original : Nat → F) (scalar start index limb : Nat)
    (before : index<126) (small : limb<2) :
    one original scalar start (start+2*index+limb)=
      if limb=0 then (window scalar index).output.x else (window scalar index).output.y := by
  have bounds : start≤start+2*index+limb ∧ start+2*index+limb<start+252 := by omega
  have quotient : (start+2*index+limb-start)/2=index := by omega
  have remainder : (start+2*index+limb-start)%2=limb := by omega
  simp only [one,if_pos bounds,quotient,remainder]

def seed (original : Nat → F) (w : TransferSem.Witness) : Nat → F := (one (one (one (one (one (one (one (one original (scalar w ⟨7,by decide⟩) 16406) (scalar w ⟨6,by decide⟩) 15144) (scalar w ⟨5,by decide⟩) 13882) (scalar w ⟨4,by decide⟩) 11864) (scalar w ⟨3,by decide⟩) 10336) (scalar w ⟨2,by decide⟩) 8804) (scalar w ⟨1,by decide⟩) 6587) (scalar w ⟨0,by decide⟩) 5183)
theorem limb0 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (5183+2*index+limb)=
      if limb=0 then (window (scalar w ⟨0,by decide⟩) index).output.x
      else (window (scalar w ⟨0,by decide⟩) index).output.y := by
  unfold seed
  exact one_limb _ _ _ index limb before small
theorem limb1 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (6587+2*index+limb)=
      if limb=0 then (window (scalar w ⟨1,by decide⟩) index).output.x
      else (window (scalar w ⟨1,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb2 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (8804+2*index+limb)=
      if limb=0 then (window (scalar w ⟨2,by decide⟩) index).output.x
      else (window (scalar w ⟨2,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  rw [one_outside _ _ 6587 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb3 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (10336+2*index+limb)=
      if limb=0 then (window (scalar w ⟨3,by decide⟩) index).output.x
      else (window (scalar w ⟨3,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  rw [one_outside _ _ 6587 _ (Or.inr (by omega))]
  rw [one_outside _ _ 8804 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb4 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (11864+2*index+limb)=
      if limb=0 then (window (scalar w ⟨4,by decide⟩) index).output.x
      else (window (scalar w ⟨4,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  rw [one_outside _ _ 6587 _ (Or.inr (by omega))]
  rw [one_outside _ _ 8804 _ (Or.inr (by omega))]
  rw [one_outside _ _ 10336 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb5 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (13882+2*index+limb)=
      if limb=0 then (window (scalar w ⟨5,by decide⟩) index).output.x
      else (window (scalar w ⟨5,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  rw [one_outside _ _ 6587 _ (Or.inr (by omega))]
  rw [one_outside _ _ 8804 _ (Or.inr (by omega))]
  rw [one_outside _ _ 10336 _ (Or.inr (by omega))]
  rw [one_outside _ _ 11864 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb6 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (15144+2*index+limb)=
      if limb=0 then (window (scalar w ⟨6,by decide⟩) index).output.x
      else (window (scalar w ⟨6,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  rw [one_outside _ _ 6587 _ (Or.inr (by omega))]
  rw [one_outside _ _ 8804 _ (Or.inr (by omega))]
  rw [one_outside _ _ 10336 _ (Or.inr (by omega))]
  rw [one_outside _ _ 11864 _ (Or.inr (by omega))]
  rw [one_outside _ _ 13882 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb7 (original : Nat → F) (w : TransferSem.Witness) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (16406+2*index+limb)=
      if limb=0 then (window (scalar w ⟨7,by decide⟩) index).output.x
      else (window (scalar w ⟨7,by decide⟩) index).output.y := by
  unfold seed
  rw [one_outside _ _ 5183 _ (Or.inr (by omega))]
  rw [one_outside _ _ 6587 _ (Or.inr (by omega))]
  rw [one_outside _ _ 8804 _ (Or.inr (by omega))]
  rw [one_outside _ _ 10336 _ (Or.inr (by omega))]
  rw [one_outside _ _ 11864 _ (Or.inr (by omega))]
  rw [one_outside _ _ 13882 _ (Or.inr (by omega))]
  rw [one_outside _ _ 15144 _ (Or.inr (by omega))]
  exact one_limb _ _ _ index limb before small
theorem limb (original : Nat → F) (w : TransferSem.Witness) (family : Fin 8) (index limb : Nat)
    (before : index<126) (small : limb<2) :
    seed original w (pointStart family+2*index+limb)=
      if limb=0 then (window (scalar w family) index).output.x else (window (scalar w family) index).output.y := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨
      family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨ family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact limb0 original w index limb before small
  · exact limb1 original w index limb before small
  · exact limb2 original w index limb before small
  · exact limb3 original w index limb before small
  · exact limb4 original w index limb before small
  · exact limb5 original w index limb before small
  · exact limb6 original w index limb before small
  · exact limb7 original w index limb before small
theorem point (original : Nat → F) (w : TransferSem.Witness) (family : Fin 8) (index : Nat) (before : index<126) :
    VariableWindowColumns449.columnPoint (seed original w) (pointStart family+2*index)=
      (window (scalar w family) index).output := by
  have x := limb original w family index 0 before (by decide)
  have y := limb original w family index 1 before (by decide)
  simp only [Nat.add_zero,if_pos rfl] at x
  simp only [if_neg (show ¬(1:Nat)=0 by decide)] at y
  cases output : (window (scalar w family) index).output with
  | mk px py =>
    simp only [output] at x y
    exact congrArg₂ Group.Point.mk x y
end ShielddSecurity.FixedFamilySeed549
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.one_outside
#print axioms ShielddSecurity.FixedFamilySeed549.one_outside
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.one_limb
#print axioms ShielddSecurity.FixedFamilySeed549.one_limb
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb0
#print axioms ShielddSecurity.FixedFamilySeed549.limb0
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb1
#print axioms ShielddSecurity.FixedFamilySeed549.limb1
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb2
#print axioms ShielddSecurity.FixedFamilySeed549.limb2
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb3
#print axioms ShielddSecurity.FixedFamilySeed549.limb3
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb4
#print axioms ShielddSecurity.FixedFamilySeed549.limb4
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb5
#print axioms ShielddSecurity.FixedFamilySeed549.limb5
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb6
#print axioms ShielddSecurity.FixedFamilySeed549.limb6
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb7
#print axioms ShielddSecurity.FixedFamilySeed549.limb7
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.limb
#print axioms ShielddSecurity.FixedFamilySeed549.limb
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySeed549.point
#print axioms ShielddSecurity.FixedFamilySeed549.point
