import ShielddSecurity.DetectionGroupDomain611
import ShielddSecurity.UserPointDomain351
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionNonidentityDomain759
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model

theorem selected_nonidentity (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    nonidentity (DetectionGroupDomain611.selected c w) := by
  obtain ⟨_,_,_,_,_,_,_,_,encryption,_⟩ := legal.2.1
  exact encryption.1

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    ((DetectionGroupDomain611.selected c w).x:F)≠0 := by
  have nonzero := selected_nonidentity c w legal
  change ((if w.regulated then w.registry.detection else DetectionGroupDomain611.defaultPoint).x:F)≠0
  cases flag : w.regulated
  · change (17832230285398775523840151435063191920633280288053987250961356462684628833490:F)≠0
    decide +kernel
  · have valid : ValidPoint (DetectionGroupDomain611.crypto c) w.registry.detection := legal.2.1.1.1
    have member := SubgroupSeedCompletion203.member_of_valid
      (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator (DetectionGroupDomain611.baseCrypto c)))
      representation model w.registry.detection valid
    have identity : nonidentity w.registry.detection := by
      change nonidentity (if w.regulated then w.registry.detection else DetectionGroupDomain611.defaultPoint) at nonzero
      simpa only [flag,if_true] using nonzero
    exact SubgroupNonidentity350.member_x_nonzero model _ member
      (UserPointDomain351.field_nonidentity _ valid.1 identity)

def seed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=1503 then ((DetectionGroupDomain611.selected c w).x:F)⁻¹ else original column

theorem selected (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    seed original c w 1503=((DetectionGroupDomain611.selected c w).x:F)⁻¹ := by
  simp only [seed,if_pos rfl,if_true]

theorem inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    seed original c w 1503*((DetectionGroupDomain611.selected c w).x:F)=1 := by
  rw [selected]
  exact inv_mul_cancel₀ (x_nonzero c w legal)
end ShielddSecurity.DetectionNonidentityDomain759

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityDomain759.selected_nonidentity
#print axioms ShielddSecurity.DetectionNonidentityDomain759.selected_nonidentity

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityDomain759.x_nonzero
#print axioms ShielddSecurity.DetectionNonidentityDomain759.x_nonzero

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityDomain759.selected
#print axioms ShielddSecurity.DetectionNonidentityDomain759.selected

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityDomain759.inverse
#print axioms ShielddSecurity.DetectionNonidentityDomain759.inverse
