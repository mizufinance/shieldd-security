import ShielddSecurity.PublishedInverseFrame591
import ShielddSecurity.PublishedInverse588
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedInverseSeed592
open ConcreteJubjubField01 TransferSem CompilerAssertionBlock51
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  match column with
  | 5435 => ((w.outputs 0).recovery.epk.x:F)⁻¹
  | 6839 => ((w.outputs 1).recovery.epk.x:F)⁻¹
  | 9056 => ((w.encryption.ownership 0).r.x:F)⁻¹
  | 10588 => ((w.encryption.ownership 1).r.x:F)⁻¹
  | 12116 => ((w.encryption.tiers 0).epk.x:F)⁻¹
  | 14134 => ((w.encryption.tiers 1).epk.x:F)⁻¹
  | 15396 => ((w.encryption.tiers 2).epk.x:F)⁻¹
  | 16658 => ((w.encryption.tiers 3).epk.x:F)⁻¹
  | _ => original column

theorem source_hint (original : Nat → F) (w : TransferSem.Witness) (family : Fin 8) :
    seed original w (PublishedInverse588.hint family)=((FixedFamilyPublished579.published w family).x:F)⁻¹ := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rfl

theorem inside (family : Fin 8) : PublishedInverseLayout589.Inside (PublishedInverse588.hint family) := by
  have member : PublishedInverse588.hint family∈PublishedInverseLayout589.starts := by
    have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
        family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
        family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
      have bound := family.isLt
      simp only [Fin.ext_iff]
      omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact ⟨PublishedInverse588.hint family,member,by omega,by omega⟩

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  PublishedPointSeed584.assignment (seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial (PublishedInverse588.hint family)=((FixedFamilyPublished579.published w family).x:F)⁻¹ := by
  unfold assignment
  rw [PublishedInverseFrame591.published_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial _ (inside family)]
  exact source_hint original w family

theorem operand_column (family : Fin 8) : PublishedInverse588.operand family=FixedPublishedRows580.rightColumn family := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rfl

theorem operand (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial (PublishedInverse588.operand family)=((FixedFamilyPublished579.published w family).x:F) := by
  unfold assignment
  rw [operand_column]
  exact congrArg Group.Point.x (PublishedPointSeed584.published_point (seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial family)

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment PublishedPointSeed584.assignment
  exact PayloadBindings565.arithmetic _ c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial CompilerArithmeticTransport41.copy=1 := by
  unfold assignment PublishedPointSeed584.assignment
  exact PayloadBindings565.copied _ c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
  unfold assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact AuthorizationRkSeed505.zero _ c w legal rkInitial authInitial initial senderInitial receiverInitial

end ShielddSecurity.PublishedInverseSeed592

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.seed
#print axioms ShielddSecurity.PublishedInverseSeed592.seed

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.source_hint
#print axioms ShielddSecurity.PublishedInverseSeed592.source_hint

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.inside
#print axioms ShielddSecurity.PublishedInverseSeed592.inside

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.assignment
#print axioms ShielddSecurity.PublishedInverseSeed592.assignment

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.hint
#print axioms ShielddSecurity.PublishedInverseSeed592.hint

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.operand_column
#print axioms ShielddSecurity.PublishedInverseSeed592.operand_column

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.operand
#print axioms ShielddSecurity.PublishedInverseSeed592.operand

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.arithmetic
#print axioms ShielddSecurity.PublishedInverseSeed592.arithmetic

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.copied
#print axioms ShielddSecurity.PublishedInverseSeed592.copied

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseSeed592.zero
#print axioms ShielddSecurity.PublishedInverseSeed592.zero
