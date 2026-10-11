from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-conditions201-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.CanonicalRecovery195
import ShielddSecurity.RegistryRecovery194
import ShielddSecurity.CapturedRegulatedSound163
import ShielddSecurity.CapturedGlobalEpoch64
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryConditions201
open PoseidonNatural192 RegistryRecovery194
open CapturedInitial73419Generic01 (p)
variable {F : Type} [Field F] [CharP F p]
theorem epoch_bound (representation : CanonicalRepresentation F) (rho : Nat → F)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 (recover representation rho).audit.epoch<2^64 :=
 CapturedGlobalEpoch64.full_canonical_bound rho _ (representation.bounded _) (representation.cast_value _) satisfied
theorem epoch_nonzero (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : (recover representation rho).audit.epoch≠0 :=
 CapturedGlobalEpoch64.full_regulated_nat rho _ (representation.cast_value _) one regulated satisfied
theorem original_values (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 representation.value (rho 11)=CapturedValueDecode158.value rho ∧
 representation.value (rho 6)=CapturedAssetDecode160.value rho ∧
 representation.value (rho 13)=CapturedNextDecode161.value rho := by
 have originals:=CapturedRegistryOrderSound162.canonical_originals rho satisfied one
 exact ⟨CanonicalRecovery195.value_unique representation _ _ originals.1.1 originals.1.2,
   CanonicalRecovery195.value_unique representation _ _ originals.2.1.1 originals.2.1.2,
   CanonicalRecovery195.value_unique representation _ _ originals.2.2.1 originals.2.2.2⟩
omit [CharP F p] in
theorem value_bounds (representation : CanonicalRepresentation F) (rho : Nat → F) :
 (recover representation rho).value<TransferCore.fieldModulus ∧
 representation.value (rho 6)<TransferCore.fieldModulus ∧
 (recover representation rho).nextValue<TransferCore.fieldModulus :=
 ⟨representation.bounded _,representation.bounded _,representation.bounded _⟩
theorem regulated_value (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10=1) : representation.value (rho 6)=(recover representation rho).value := by
 have originals:=original_values representation rho one satisfied
 change representation.value (rho 6)=representation.value (rho 11)
 rw [originals.1,originals.2.1]
 exact CapturedRegulatedSound163.regulated_equal rho satisfied one regulated
theorem unregulated_order (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (unregulated : rho 10=0) :
 (recover representation rho).value<representation.value (rho 6) ∧
 representation.value (rho 6)<(recover representation rho).nextValue := by
 have originals:=original_values representation rho one satisfied
 change representation.value (rho 11)<representation.value (rho 6) ∧
   representation.value (rho 6)<representation.value (rho 13)
 rw [originals.1,originals.2.1,originals.2.2]
 exact CapturedRegistryOrderSound162.unregulated rho satisfied one unregulated
end ShielddSecurity.RegistryConditions201
'''
pins=[W/'mac-registry-conditions201-source01/producer-manifest01.json',W/'mac-canonical-recovery195-source02/source-root/ShielddSecurity/CanonicalRecovery195.lean',W/'mac-registry-recovery194-source01/source-root/ShielddSecurity/RegistryRecovery194.lean',W/'mac-regulated-sound163-source01/source-root/ShielddSecurity/CapturedRegulatedSound163.lean',W/'mac-global-epoch64-source02/source-root/ShielddSecurity/CapturedGlobalEpoch64.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'RegistryConditions201':dict(body=body,names=['epoch_bound','epoch_nonzero','original_values','value_bounds','regulated_value','unregulated_order'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Full captured relation derives recovered epoch/range/nonzero and canonical value/asset/next order from existing exact row certificates. No desired RegistrySem, semantic inequality, or assertion-truth premise; no native Crypto association. Six planned full type/standard axiom reports.'),sort_keys=True,separators=(',',':'))+'\n')
