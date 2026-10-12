import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.CandidateMerkleMeaning261
import ShielddSecurity.CapturedMerkleIntegerRoot191
import ShielddSecurity.MerkleNaturalRoot197
import ShielddSecurity.CapturedAnchorRowSound165
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedMerklePosition264
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 PoseidonNatural192
open WordHints210
-- Exact owned32-bit position slot; neither bit truth nor hash truth is a premise.
theorem position_entry : (CapturedWordSlots211B000.W01.slot,CapturedWordSlots211B000.W01.first)∈CapturedWordRoot213.words := by
 unfold CapturedWordRoot213.words
 exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem encoded_bit (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (i : Fin 32) : SharedWordWitness221.bits numbers fallback (184+i.val)=CapturedMerklePositionGlobal190.bits (numbers 135) i := by
 have equal:=SharedWordWitness221.encoded numbers fallback coherent
   (CapturedWordSlots211B000.W01.slot,CapturedWordSlots211B000.W01.first) position_entry
 have each:=congrArg (fun xs : List Bool => xs[i.val]?) equal
 change ((List.range' 184 32).map (SharedWordWitness221.bits numbers fallback))[i.val]?=(encodeBits 32 (numbers 135))[i.val]? at each
 have leftBound : i.val<((List.range' 184 32).map (SharedWordWitness221.bits numbers fallback)).length := by
   simpa only [List.length_map,List.length_range'] using i.isLt
 have rightBound : i.val<(encodeBits 32 (numbers 135)).length := by
   simpa only [encodeBits_length] using i.isLt
 rw [List.getElem?_eq_getElem leftBound,List.getElem?_eq_getElem rightBound] at each
 exact (by simpa only [List.getElem_map,List.getElem_range',Nat.one_mul,CapturedMerklePositionGlobal190.bits] using Option.some.inj each)
variable {F : Type} [Field F]
theorem encoding (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (i : Fin 32) : SharedWordWitness221.completed base numbers fallback (184+i.val)=
 MerkleQuaternary30.boolValue (CapturedMerklePositionGlobal190.bits (numbers 135) i) := by
 have member : 184+i.val∈WordHints210.columns CapturedWordSlots211B000.W01.slot :=
   List.mem_range'.mpr ⟨i.val,i.isLt,by simp only [Nat.one_mul]⟩
 have seedMember:=SharedWordWitness221.word_coverage
   (CapturedWordSlots211B000.W01.slot,CapturedWordSlots211B000.W01.first) position_entry _ member
 have original := CapturedFullRelation58.candidate_inputs
   (SharedWordWitness221.seeded base numbers fallback) (181+i.val) (by have bound:=i.isLt;omega)
 have same : 3+(181+i.val)=184+i.val := by omega
 rw [same] at original
 change SharedWordWitness221.completed base numbers fallback (184+i.val)=_ at original
 calc
  SharedWordWitness221.completed base numbers fallback (184+i.val)=SharedWordWitness221.seeded base numbers fallback (184+i.val) := original
  _=BooleanHints207.bitValue (SharedWordWitness221.bits numbers fallback (184+i.val)) := BooleanHints207.seeded_selected base _ _ _ seedMember
  _=MerkleQuaternary30.boolValue (CapturedMerklePositionGlobal190.bits (numbers 135) i) := congrArg (fun bit : Bool => if bit then (1:F) else 0) (encoded_bit numbers fallback coherent i)
variable [CharP F p]
theorem integer_output (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers)) :
 eval (SharedWordWitness221.completed base numbers fallback) MerklePath33AnchorData.output=
 CapturedMerkleIntegerRoot191.root (SharedWordWitness221.completed base numbers fallback) (numbers 135) 16 := by
 have result:=CandidateMerkleMeaning261.output (SharedWordWitness221.seeded base numbers fallback)
   ((SharedWordWitness221.seeded_fixed base numbers fallback).1.trans one)
 rw [MerkleOrdered34.meaning_eq _ _ (encoding base numbers fallback coherent) 15 (by decide)] at result
 exact result.trans (CapturedMerkleIntegerRoot191.root_eq _ _ 16)
theorem position_value (representation : CanonicalRepresentation F)
 (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (bound : numbers 135<2^32)
 (meaning : SharedWordWitness221.seeded base numbers fallback 135=(numbers 135:F)) :
 representation.value (SharedWordWitness221.completed base numbers fallback 135)=numbers 135 := by
 apply CanonicalRecovery195.value_unique
 · exact lt_trans bound (by decide : 2^32<p)
 · exact ((CapturedFullRelation58.candidate_inputs (SharedWordWitness221.seeded base numbers fallback) 132 (by decide)).trans meaning).symm
theorem natural_output (representation : CanonicalRepresentation F) (c : TransferSem.Crypto)
 (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (bound : numbers 135<2^32)
 (meaning : SharedWordWitness221.seeded base numbers fallback 135=(numbers 135:F)) :
 (TransferSem.root (withHash c RegistryNatural193.small RegistryNatural193.wide representation) .asset
   (RegistryRecovery194.recover representation (SharedWordWitness221.completed base numbers fallback)).position
   (TransferSem.assetLeaf (withHash c RegistryNatural193.small RegistryNatural193.wide representation)
     (RegistryRecovery194.recover representation (SharedWordWitness221.completed base numbers fallback)))
   (RegistryRecovery194.recover representation (SharedWordWitness221.completed base numbers fallback)).siblings:F)=
 eval (SharedWordWitness221.completed base numbers fallback) MerklePath33AnchorData.output := by
 have cast:=MerkleNaturalRoot197.root_cast representation (SharedWordWitness221.completed base numbers fallback) c
 have position : (RegistryRecovery194.recover representation (SharedWordWitness221.completed base numbers fallback)).position=numbers 135 := position_value representation base numbers fallback bound meaning
 rw [position] at cast
 exact cast.trans (integer_output base numbers fallback one coherent).symm
theorem anchor_from_legal (representation : CanonicalRepresentation F) (c : TransferSem.Crypto)
 (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (bound : numbers 135<2^32)
 (meaning : SharedWordWitness221.seeded base numbers fallback 135=(numbers 135:F))
 (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash c RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation (SharedWordWitness221.completed base numbers fallback)=w.registry)
 (anchor : representation.value (SharedWordWitness221.completed base numbers fallback 4)=w.assetAnchor) :
 ∃ row,CapturedFullRelation58.rowAt 178117=some row ∧
 Square (eval (SharedWordWitness221.completed base numbers fallback) row.a) (eval (SharedWordWitness221.completed base numbers fallback) row.b) := by
 let rho:=SharedWordWitness221.completed base numbers fallback
 have value:=natural_output representation c base numbers fallback one coherent bound meaning
 rw [registry] at value
 rcases legal with ⟨_,_,_,_,_,_,_,_,_,root,_⟩
 rw [root,←anchor,representation.cast_value] at value
 have truth : Truth rho (.linear MerklePath33AnchorData.output [(4,1)]) := by
   change eval rho MerklePath33AnchorData.output=eval rho [(4,1)]
   simpa only [eval,Int.cast_one,one_mul,add_zero] using value.symm
 obtain ⟨row,hint,found,recipe,checked⟩:=CapturedFullAssertions54.block.exact_checked 163 (by decide)
 have same : hint=(true,.linear MerklePath33AnchorData.output [(4,1)]) :=
   Option.some.inj (recipe.symm.trans CapturedAnchorRowSound165.recipe_exact)
 subst hint
 refine ⟨row,(CapturedFullRelation58.assertion_position 163 (by decide)).trans found,?_⟩
 exact (CompilerAssertionBlock51.checked_iff copy row _ checked rho
   (CapturedFullRelation58.candidate_links (SharedWordWitness221.seeded base numbers fallback)).2.2).mpr truth
end ShielddSecurity.SharedMerklePosition264

set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.position_entry
#print axioms ShielddSecurity.SharedMerklePosition264.position_entry
set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.encoded_bit
#print axioms ShielddSecurity.SharedMerklePosition264.encoded_bit
set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.encoding
#print axioms ShielddSecurity.SharedMerklePosition264.encoding
set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.integer_output
#print axioms ShielddSecurity.SharedMerklePosition264.integer_output
set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.position_value
#print axioms ShielddSecurity.SharedMerklePosition264.position_value
set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.natural_output
#print axioms ShielddSecurity.SharedMerklePosition264.natural_output
set_option pp.all true in
#check @ShielddSecurity.SharedMerklePosition264.anchor_from_legal
#print axioms ShielddSecurity.SharedMerklePosition264.anchor_from_legal
