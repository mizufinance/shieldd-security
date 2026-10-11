import ShielddSecurity.CanonicalRecovery195
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

set_option pp.all true in
#check @ShielddSecurity.RegistryConditions201.epoch_bound
#print axioms ShielddSecurity.RegistryConditions201.epoch_bound
set_option pp.all true in
#check @ShielddSecurity.RegistryConditions201.epoch_nonzero
#print axioms ShielddSecurity.RegistryConditions201.epoch_nonzero
set_option pp.all true in
#check @ShielddSecurity.RegistryConditions201.original_values
#print axioms ShielddSecurity.RegistryConditions201.original_values
set_option pp.all true in
#check @ShielddSecurity.RegistryConditions201.value_bounds
#print axioms ShielddSecurity.RegistryConditions201.value_bounds
set_option pp.all true in
#check @ShielddSecurity.RegistryConditions201.regulated_value
#print axioms ShielddSecurity.RegistryConditions201.regulated_value
set_option pp.all true in
#check @ShielddSecurity.RegistryConditions201.unregulated_order
#print axioms ShielddSecurity.RegistryConditions201.unregulated_order
