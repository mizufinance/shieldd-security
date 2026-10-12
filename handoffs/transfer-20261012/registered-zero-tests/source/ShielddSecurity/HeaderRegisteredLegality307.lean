import ShielddSecurity.HeaderRegistrySeed299
import ShielddSecurity.SharedRegisteredAssertions306
import ShielddSecurity.CapturedRegistryPointDomain75
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.HeaderRegisteredLegality307
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
def base (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) : Nat → F :=
  CapturedGlobalEpoch64.prepared (HeaderRegistrySeed299.combined original c w) w.registry.audit.epoch

theorem header_payload_x (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    HeaderRegistrySeed299.combined original c w 35 = (w.registry.audit.payload.x : F) := by
  exact RegistryNaturalSeed298.seed_fixed _ _ 35 (by simp [RegistryNaturalSeed298.fixedColumns])

theorem header_payload_y (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    HeaderRegistrySeed299.combined original c w 36 = (w.registry.audit.payload.y : F) := by
  exact RegistryNaturalSeed298.seed_fixed _ _ 36 (by simp [RegistryNaturalSeed298.fixedColumns])

theorem header_checking_x (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    HeaderRegistrySeed299.combined original c w 42 = (w.registry.audit.checking.x : F) := by
  exact RegistryNaturalSeed298.seed_fixed _ _ 42 (by simp [RegistryNaturalSeed298.fixedColumns])

theorem header_checking_y (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    HeaderRegistrySeed299.combined original c w 43 = (w.registry.audit.checking.y : F) := by
  exact RegistryNaturalSeed298.seed_fixed _ _ 43 (by simp [RegistryNaturalSeed298.fixedColumns])

theorem legal_guards (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : RegistrySem (crypto c) w) : CapturedRegisteredHints72.LegalGuards (base original c w) :=
  CapturedRegistryPointDomain75.registry_coordinate_guards (crypto c) w legal rfl
    (HeaderRegistrySeed299.combined original c w) w.registry.audit.epoch
    (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.2.2
    (header_payload_x original c w) (header_payload_y original c w)
    (header_checking_x original c w) (header_checking_y original c w)
    (HeaderRegistrySeed299.original_headers original c w).1

theorem base_zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    base original c w 0 = 1 := by
  exact (CapturedEpochHints62.seeded_outside _ w.registry.audit.epoch 0 (by decide)).trans
    ((CompilerVerifierLinks53.seeded_outside (HeaderRegistrySeed299.combined original c w) 0 (by decide)).trans
      (HeaderRegistrySeed299.original_headers original c w).1)

theorem base_control (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) :
    base original c w 10 = 0 ∨ base original c w 10 = 1 := by
  have same : base original c w 10 = HeaderRegistrySeed299.combined original c w 10 :=
    (CapturedEpochHints62.seeded_outside _ w.registry.audit.epoch 10 (by decide)).trans
      (CompilerVerifierLinks53.seeded_outside (HeaderRegistrySeed299.combined original c w) 10 (by decide))
  have meaning := (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.2.2
  rw [same,meaning]
  cases w.regulated <;> simp

theorem registered_assertions (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (numbers : Nat → Nat) (legal : RegistrySem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt
      (SharedZeroPrimitives305.completed (base original c w) numbers) CapturedRegisteredAudit70.block.actual 35 :=
  SharedRegisteredAssertions306.completed_assertions (base original c w) numbers
    (base_zero original c w) (base_control original c w) (legal_guards original c w legal)
end ShielddSecurity.HeaderRegisteredLegality307

