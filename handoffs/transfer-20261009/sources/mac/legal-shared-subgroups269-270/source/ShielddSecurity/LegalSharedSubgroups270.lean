import ShielddSecurity.SharedSubgroups269
import ShielddSecurity.SubgroupSeedCompletion203
import ShielddSecurity.OriginalAnchor266
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalSharedSubgroups270
open Compiler CompilerArithmeticTransport41 PoseidonNatural192
variable {F J : Type} [Field F] [AddCommGroup J]
theorem field_encode (representation : CanonicalRepresentation F) (point : Group.Point F) :
 SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation point)=point := by
 cases point
 simp only [SubgroupSeedCompletion203.fieldPoint,RegistryPointSemantic200.encode,representation.cast_value]
theorem member_encoded (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) (point : Group.Point F)
 (valid : TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model)
   (RegistryPointSemantic200.encode representation point)) : CapturedSubgroupModel199.Member model point := by
 have member:=SubgroupSeedCompletion203.member_of_valid c representation model _ valid
 rw [field_encode] at member
 exact member
theorem members_from_legal (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry) :
 ∀ group,CapturedSubgroupModel199.Member model (CapturedFourSubgroupSeed89.Claimed base group) := by
 rcases legal with ⟨detection,ring,payload,checking,_,_,_,_,_,_,_⟩
 intro group
 apply member_encoded c representation model
 rcases group with ⟨group,before⟩
 interval_cases group
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).detection
   rw [registry]
   exact detection
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).ring
   rw [registry]
   exact ring
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).audit.payload
   rw [registry]
   exact payload
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).audit.checking
   rw [registry]
   exact checking
theorem legal_preimages (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry) :
 ∃ initial : Fin 4 → Group.Point F,
 (∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group)) ∧
 ∀ group,CapturedFourSubgroupSeed89.Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group) :=
 SubgroupSeedCompletion203.exists_initial model imaginary nonSquare imaginarySquare base
   (members_from_legal c representation model base w legal registry)
variable [CharP F p]
theorem shared_groups_and_anchor (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (position : numbers 135=representation.value (base 135)) (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry)
 (anchor : representation.value (base 4)=w.assetAnchor) :
 ∃ initial : Fin 4 → Group.Point F,
 (∀ group,Satisfies (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback)
   (CapturedFourSubgroupConstructor88.originalRows group)) ∧
 ∃ row,CapturedFullRelation58.rowAt 178117=some row ∧
 Square (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) row.a)
   (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) row.b) := by
 obtain ⟨initial,valid,binding⟩:=legal_preimages c representation model base imaginary nonSquare imaginarySquare w legal registry
 refine ⟨initial,SharedSubgroups269.all_four base initial numbers fallback imaginary one binding valid nonSquare imaginarySquare,?_⟩
 have rawZero : CapturedFourSubgroupSeed89.seeded base initial 0=1 :=
   (CapturedFourSubgroupSeed89.seeded_outside base initial 0 (by decide)).trans one
 have rawPosition : numbers 135=representation.value (CapturedFourSubgroupSeed89.seeded base initial 135) :=
   position.trans (congrArg representation.value (CapturedFourSubgroupSeed89.seeded_outside base initial 135 (by decide))).symm
 exact OriginalAnchor266.anchor_from_original representation (RegistryPointSemantic200.interpret c representation model)
   (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback rawZero coherent rawPosition w legal
   ((SharedSubgroups269.recover_frame representation base initial).trans registry)
   ((SharedSubgroups269.anchor_frame representation base initial).trans anchor)
end ShielddSecurity.LegalSharedSubgroups270

set_option pp.all true in
#check @ShielddSecurity.LegalSharedSubgroups270.field_encode
#print axioms ShielddSecurity.LegalSharedSubgroups270.field_encode
set_option pp.all true in
#check @ShielddSecurity.LegalSharedSubgroups270.member_encoded
#print axioms ShielddSecurity.LegalSharedSubgroups270.member_encoded
set_option pp.all true in
#check @ShielddSecurity.LegalSharedSubgroups270.members_from_legal
#print axioms ShielddSecurity.LegalSharedSubgroups270.members_from_legal
set_option pp.all true in
#check @ShielddSecurity.LegalSharedSubgroups270.legal_preimages
#print axioms ShielddSecurity.LegalSharedSubgroups270.legal_preimages
set_option pp.all true in
#check @ShielddSecurity.LegalSharedSubgroups270.shared_groups_and_anchor
#print axioms ShielddSecurity.LegalSharedSubgroups270.shared_groups_and_anchor
