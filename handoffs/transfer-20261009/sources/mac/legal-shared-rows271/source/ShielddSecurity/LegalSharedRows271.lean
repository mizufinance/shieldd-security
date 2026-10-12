import ShielddSecurity.LegalSharedSubgroups270
import ShielddSecurity.SharedMerkleWitness263
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalSharedRows271
open Compiler CompilerArithmeticTransport41 PoseidonNatural192 WordHints210
theorem values_checked : CapturedWordRoot213.words.all
 (fun entry => decide (entry.1.value∉CapturedFourSubgroupSeed89.hintColumns))=true := by decide +kernel
theorem values_outside (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words) :
 entry.1.value∉CapturedFourSubgroupSeed89.hintColumns :=
 of_decide_eq_true ((List.all_eq_true.mp values_checked) entry member)
variable {F : Type} [Field F]
theorem seeded_frame (base : Nat → F) (initial : Fin 4 → Group.Point F)
 (numbers : Nat → Nat) (fallback : Nat → Bool) (column : Nat)
 (outside : column∉CapturedFourSubgroupSeed89.hintColumns) :
 SharedWordWitness221.seeded (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback column=
 SharedWordWitness221.seeded base numbers fallback column := by
 by_cases selected : column∈SharedWordWitness221.seedColumns
 · exact (BooleanHints207.seeded_selected _ _ _ column selected).trans
     (BooleanHints207.seeded_selected _ _ _ column selected).symm
 · exact (BooleanHints207.seeded_outside _ _ _ column selected).trans
     ((CapturedFourSubgroupSeed89.seeded_outside base initial column outside).trans
       (BooleanHints207.seeded_outside _ _ _ column selected).symm)
variable [CharP F p]
def Rows (rho : Nat → F) : Prop :=
 CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 ∧
 (∀ slot∈CapturedBooleanRoot209.slots,∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval rho row.a) (eval rho row.b)) ∧
 ∀ entry∈CapturedWordRoot213.words,∃ row,CapturedFullRelation58.rowAt (177954+entry.1.position)=some row ∧
 Square (eval rho row.a) (eval rho row.b)
theorem shared_rows (base : Nat → F) (initial : Fin 4 → Group.Point F)
 (numbers : Nat → Nat) (fallback : Nat → Bool)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (bounded : ∀ entry∈CapturedWordRoot213.words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈CapturedWordRoot213.words,SharedWordWitness221.seeded base numbers fallback entry.1.value=(numbers entry.1.value:F)) :
 Rows (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) := by
 refine ⟨SharedWordWitness221.arithmetic _ numbers fallback,SharedWordWitness221.boolean_rows _ numbers fallback,?_⟩
 apply SharedWordWitness221.word_rows _ numbers fallback coherent bounded
 intro entry member
 exact (seeded_frame base initial numbers fallback entry.1.value (values_outside entry member)).trans (meanings entry member)
variable {J : Type} [AddCommGroup J]
theorem legal_completed (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (bounded : ∀ entry∈CapturedWordRoot213.words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈CapturedWordRoot213.words,SharedWordWitness221.seeded base numbers fallback entry.1.value=(numbers entry.1.value:F))
 (position : numbers 135=representation.value (base 135)) (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry)
 (anchor : representation.value (base 4)=w.assetAnchor) :
 ∃ initial : Fin 4 → Group.Point F,
 Rows (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) ∧
 (∀ group,Satisfies (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback)
   (CapturedFourSubgroupConstructor88.originalRows group)) ∧
 ∃ row,CapturedFullRelation58.rowAt 178117=some row ∧
 Square (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) row.a)
   (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) row.b) := by
 obtain ⟨initial,groups,anchorRow⟩:=LegalSharedSubgroups270.shared_groups_and_anchor c representation model base imaginary
   nonSquare imaginarySquare numbers fallback one coherent position w legal registry anchor
 exact ⟨initial,shared_rows base initial numbers fallback coherent bounded meanings,groups,anchorRow⟩
end ShielddSecurity.LegalSharedRows271

set_option pp.all true in
#check @ShielddSecurity.LegalSharedRows271.values_checked
#print axioms ShielddSecurity.LegalSharedRows271.values_checked
set_option pp.all true in
#check @ShielddSecurity.LegalSharedRows271.values_outside
#print axioms ShielddSecurity.LegalSharedRows271.values_outside
set_option pp.all true in
#check @ShielddSecurity.LegalSharedRows271.seeded_frame
#print axioms ShielddSecurity.LegalSharedRows271.seeded_frame
set_option pp.all true in
#check @ShielddSecurity.LegalSharedRows271.Rows
#print axioms ShielddSecurity.LegalSharedRows271.Rows
set_option pp.all true in
#check @ShielddSecurity.LegalSharedRows271.shared_rows
#print axioms ShielddSecurity.LegalSharedRows271.shared_rows
set_option pp.all true in
#check @ShielddSecurity.LegalSharedRows271.legal_completed
#print axioms ShielddSecurity.LegalSharedRows271.legal_completed
