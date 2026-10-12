import ShielddSecurity.ConcreteFieldParameters280
import ShielddSecurity.LegalWordEncoding278
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ConcreteLegalEncoding283
open Compiler CompilerArithmeticTransport41 PoseidonNatural192 WordHints210 LegalWordNormalization272
abbrev F := ConcreteFieldParameters280.F
def representation : CanonicalRepresentation F := ConcreteRepresentation274.representation
theorem legal_completed {J : Type} [AddCommGroup J] (c : TransferSem.Crypto)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F) (numbers : Nat → Nat) (old : Nat → Bool)
 (one : base 0=1)
 (otherBound : ∀ entry∈CapturedWordRoot213.words,¬Alias entry.1.value → numbers entry.1.value<2^entry.1.width)
 (original : ∀ entry∈CapturedWordRoot213.words,¬Alias entry.1.value → base entry.1.value=(numbers entry.1.value:F))
 (position : numbers 135=representation.value (base 135)) (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry)
 (anchor : representation.value (base 4)=w.assetAnchor) :
 ∃ initial : Fin 4 → Group.Point F,
 LegalSharedRows271.Rows (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial)
  (normalized numbers) (LegalAliasMeanings276.fallback numbers old)) ∧
 (∀ group,Satisfies (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial)
  (normalized numbers) (LegalAliasMeanings276.fallback numbers old)) (CapturedFourSubgroupConstructor88.originalRows group)) ∧
 ∃ row,CapturedFullRelation58.rowAt 178117=some row ∧
 Square (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial)
  (normalized numbers) (LegalAliasMeanings276.fallback numbers old)) row.a)
  (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial)
  (normalized numbers) (LegalAliasMeanings276.fallback numbers old)) row.b) := by
 exact LegalWordEncoding278.legal_completed c representation model base
  ConcreteFieldParameters280.imaginary ConcreteFieldParameters280.captured_no_unit_square
  ConcreteFieldParameters280.imaginary_square numbers old one otherBound original position w legal registry anchor
end ShielddSecurity.ConcreteLegalEncoding283

set_option pp.all true in
#check @ShielddSecurity.ConcreteLegalEncoding283.F
#print axioms ShielddSecurity.ConcreteLegalEncoding283.F
set_option pp.all true in
#check @ShielddSecurity.ConcreteLegalEncoding283.representation
#print axioms ShielddSecurity.ConcreteLegalEncoding283.representation
set_option pp.all true in
#check @ShielddSecurity.ConcreteLegalEncoding283.legal_completed
#print axioms ShielddSecurity.ConcreteLegalEncoding283.legal_completed
