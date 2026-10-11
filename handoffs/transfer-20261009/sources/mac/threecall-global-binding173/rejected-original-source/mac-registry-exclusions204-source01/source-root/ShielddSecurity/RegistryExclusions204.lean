import ShielddSecurity.RegistryRecovery194
import ShielddSecurity.CapturedRegistryPointDomain75
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryExclusions204
open PoseidonNatural192 RegistryRecovery194 CapturedRegistryPointDomain75
open CompilerArithmeticTransport41 (p)
variable {F : Type} [Field F] [CharP F p]
theorem payload_identity (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : (recover representation rho).audit.payload≠(⟨0,1⟩ : TransferCore.Affine) := by
 intro same
 have hx:=congrArg (fun point : TransferCore.Affine => (point.x:F)) same
 have hy:=congrArg (fun point : TransferCore.Affine => (point.y:F)) same
 change (representation.value (rho 35):F)=(0:F) at hx
 change (representation.value (rho 36):F)=(1:F) at hy
 simp only [representation.cast_value] at hx hy
 apply regulated
 apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied 0 (by decide)
 constructor
 · rw [meaning_value rho 0 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
 · rw [meaning_value rho 1 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
theorem payload_sink (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : (recover representation rho).audit.payload≠sink := by
 intro same
 have hx:=congrArg (fun point : TransferCore.Affine => (point.x:F)) same
 have hy:=congrArg (fun point : TransferCore.Affine => (point.y:F)) same
 change (representation.value (rho 35):F)=(sink.x:F) at hx
 change (representation.value (rho 36):F)=(sink.y:F) at hy
 simp only [representation.cast_value] at hx hy
 apply regulated
 apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied 1 (by decide)
 constructor
 · rw [meaning_value rho 2 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
 · rw [meaning_value rho 3 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
theorem payload_checking (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : (recover representation rho).audit.payload≠(recover representation rho).audit.checking := by
 intro same
 have hx:=congrArg (fun point : TransferCore.Affine => (point.x:F)) same
 have hy:=congrArg (fun point : TransferCore.Affine => (point.y:F)) same
 change (representation.value (rho 35):F)=(representation.value (rho 42):F) at hx
 change (representation.value (rho 36):F)=(representation.value (rho 43):F) at hy
 simp only [representation.cast_value] at hx hy
 apply regulated
 apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied 2 (by decide)
 constructor
 · rw [meaning_value rho 4 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
 · rw [meaning_value rho 5 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
theorem checking_identity (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : (recover representation rho).audit.checking≠(⟨0,1⟩ : TransferCore.Affine) := by
 intro same
 have hx:=congrArg (fun point : TransferCore.Affine => (point.x:F)) same
 have hy:=congrArg (fun point : TransferCore.Affine => (point.y:F)) same
 change (representation.value (rho 42):F)=(0:F) at hx
 change (representation.value (rho 43):F)=(1:F) at hy
 simp only [representation.cast_value] at hx hy
 apply regulated
 apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied 3 (by decide)
 constructor
 · rw [meaning_value rho 6 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
 · rw [meaning_value rho 7 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
theorem checking_sink (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : (recover representation rho).audit.checking≠sink := by
 intro same
 have hx:=congrArg (fun point : TransferCore.Affine => (point.x:F)) same
 have hy:=congrArg (fun point : TransferCore.Affine => (point.y:F)) same
 change (representation.value (rho 42):F)=(sink.x:F) at hx
 change (representation.value (rho 43):F)=(sink.y:F) at hy
 simp only [representation.cast_value] at hx hy
 apply regulated
 apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied 4 (by decide)
 constructor
 · rw [meaning_value rho 8 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
 · rw [meaning_value rho 9 (by decide)]
   simp [meaningTerms,Compiler.eval,one,hx,hy,sink]
theorem all_guards (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) :
 (recover representation rho).audit.payload≠⟨0,1⟩ ∧
 (recover representation rho).audit.checking≠⟨0,1⟩ ∧
 (recover representation rho).audit.payload≠sink ∧
 (recover representation rho).audit.checking≠sink ∧
 (recover representation rho).audit.payload≠(recover representation rho).audit.checking :=
 ⟨payload_identity representation rho one satisfied regulated,
 checking_identity representation rho one satisfied regulated,
 payload_sink representation rho one satisfied regulated,
 checking_sink representation rho one satisfied regulated,
 payload_checking representation rho one satisfied regulated⟩
end ShielddSecurity.RegistryExclusions204

set_option pp.all true in
#check @ShielddSecurity.RegistryExclusions204.payload_identity
#print axioms ShielddSecurity.RegistryExclusions204.payload_identity
set_option pp.all true in
#check @ShielddSecurity.RegistryExclusions204.payload_sink
#print axioms ShielddSecurity.RegistryExclusions204.payload_sink
set_option pp.all true in
#check @ShielddSecurity.RegistryExclusions204.payload_checking
#print axioms ShielddSecurity.RegistryExclusions204.payload_checking
set_option pp.all true in
#check @ShielddSecurity.RegistryExclusions204.checking_identity
#print axioms ShielddSecurity.RegistryExclusions204.checking_identity
set_option pp.all true in
#check @ShielddSecurity.RegistryExclusions204.checking_sink
#print axioms ShielddSecurity.RegistryExclusions204.checking_sink
set_option pp.all true in
#check @ShielddSecurity.RegistryExclusions204.all_guards
#print axioms ShielddSecurity.RegistryExclusions204.all_guards
