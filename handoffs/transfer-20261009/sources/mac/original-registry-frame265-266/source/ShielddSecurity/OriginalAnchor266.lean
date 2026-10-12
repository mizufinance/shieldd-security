import ShielddSecurity.SharedMerklePosition264
import ShielddSecurity.RegistrySeedFrame265
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OriginalAnchor266
open Compiler CompilerArithmeticTransport41 PoseidonNatural192
variable {F : Type} [Field F]
theorem seeded_position (representation : CanonicalRepresentation F)
 (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (encoding : numbers 135=representation.value (base 135)) :
 SharedWordWitness221.seeded base numbers fallback 135=(numbers 135:F) := by
 have original:=RegistrySeedFrame265.seeded_frame base numbers fallback 135 (by constructor <;> omega)
 rw [encoding]
 exact original.trans (representation.cast_value (base 135)).symm
variable [CharP F p]
theorem anchor_from_original (representation : CanonicalRepresentation F) (c : TransferSem.Crypto)
 (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (position : numbers 135=representation.value (base 135))
 (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash c RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry)
 (anchor : representation.value (base 4)=w.assetAnchor) :
 ∃ row,CapturedFullRelation58.rowAt 178117=some row ∧
 Square (eval (SharedWordWitness221.completed base numbers fallback) row.a) (eval (SharedWordWitness221.completed base numbers fallback) row.b) := by
 have positionBound : w.registry.position<2^32 := by
   rcases legal with ⟨_,_,_,_,_,bound,_,_,_,_,_⟩
   exact bound
 have bound : numbers 135<2^32 := by
   rw [position]
   change (RegistryRecovery194.recover representation base).position<2^32
   rw [registry]
   exact positionBound
 exact SharedMerklePosition264.anchor_from_legal representation c base numbers fallback one coherent bound
   (seeded_position representation base numbers fallback position) w legal
   ((RegistrySeedFrame265.recover_frame representation base numbers fallback).trans registry)
   ((RegistrySeedFrame265.anchor_frame representation base numbers fallback).trans anchor)
end ShielddSecurity.OriginalAnchor266

set_option pp.all true in
#check @ShielddSecurity.OriginalAnchor266.seeded_position
#print axioms ShielddSecurity.OriginalAnchor266.seeded_position
set_option pp.all true in
#check @ShielddSecurity.OriginalAnchor266.anchor_from_original
#print axioms ShielddSecurity.OriginalAnchor266.anchor_from_original
