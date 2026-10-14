import ShielddSecurity.PublishedPointFrame583
import ShielddSecurity.FixedFamilyPublished579
import ShielddSecurity.FixedPublishedRows580
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedPointSeed584
open ConcreteJubjubField01 TransferSem
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  match column with
  | 4922 => ((w.outputs 0).recovery.epk.x:F)
  | 4923 => ((w.outputs 0).recovery.epk.y:F)
  | 6326 => ((w.outputs 1).recovery.epk.x:F)
  | 6327 => ((w.outputs 1).recovery.epk.y:F)
  | 8547 => ((w.encryption.ownership 0).r.x:F)
  | 8548 => ((w.encryption.ownership 0).r.y:F)
  | 10079 => ((w.encryption.ownership 1).r.x:F)
  | 10080 => ((w.encryption.ownership 1).r.y:F)
  | 8515 => ((w.encryption.tiers 0).epk.x:F)
  | 8516 => ((w.encryption.tiers 0).epk.y:F)
  | 8520 => ((w.encryption.tiers 1).epk.x:F)
  | 8521 => ((w.encryption.tiers 1).epk.y:F)
  | 8526 => ((w.encryption.tiers 2).epk.x:F)
  | 8527 => ((w.encryption.tiers 2).epk.y:F)
  | 8531 => ((w.encryption.tiers 3).epk.x:F)
  | 8532 => ((w.encryption.tiers 3).epk.y:F)
  | _ => original column

theorem source_point (original : Nat → F) (w : TransferSem.Witness) (family : Fin 8) :
    VariableWindowColumns449.columnPoint (seed original w) (FixedPublishedRows580.rightColumn family)=
      SubgroupSeedCompletion203.fieldPoint (FixedFamilyPublished579.published w family) := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem inside (family : Fin 8) (limb : Nat) (small : limb<2) :
    PublishedPointLayout581.Inside (FixedPublishedRows580.rightColumn family+limb) := by
  have member : FixedPublishedRows580.rightColumn family∈PublishedPointLayout581.starts := by
    have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
        family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
        family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
      have bound := family.isLt
      simp only [Fin.ext_iff]
      omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨FixedPublishedRows580.rightColumn family,member,by omega,by omega⟩

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  PayloadBindings565.assignment (seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem published_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (FixedPublishedRows580.rightColumn family)=
      SubgroupSeedCompletion203.fieldPoint (FixedFamilyPublished579.published w family) := by
  unfold assignment
  have x := PublishedPointFrame583.payload_frame (seed original w) c w legal rkInitial authInitial initial
    senderInitial receiverInitial (FixedPublishedRows580.rightColumn family+0) (inside family 0 (by decide))
  have y := PublishedPointFrame583.payload_frame (seed original w) c w legal rkInitial authInitial initial
    senderInitial receiverInitial (FixedPublishedRows580.rightColumn family+1) (inside family 1 (by decide))
  simp only [Nat.add_zero] at x
  exact (congrArg₂ Group.Point.mk x y).trans (source_point original w family)

end ShielddSecurity.PublishedPointSeed584

set_option pp.all true in
#check @ShielddSecurity.PublishedPointSeed584.seed
#print axioms ShielddSecurity.PublishedPointSeed584.seed

set_option pp.all true in
#check @ShielddSecurity.PublishedPointSeed584.source_point
#print axioms ShielddSecurity.PublishedPointSeed584.source_point

set_option pp.all true in
#check @ShielddSecurity.PublishedPointSeed584.inside
#print axioms ShielddSecurity.PublishedPointSeed584.inside

set_option pp.all true in
#check @ShielddSecurity.PublishedPointSeed584.assignment
#print axioms ShielddSecurity.PublishedPointSeed584.assignment

set_option pp.all true in
#check @ShielddSecurity.PublishedPointSeed584.published_point
#print axioms ShielddSecurity.PublishedPointSeed584.published_point
