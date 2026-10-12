import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.CapturedWordCompatibility251
import ShielddSecurity.CandidateMerkleMeaning261
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedMerkleWitness263
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem path (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1) :
 eval (SharedWordWitness221.completed base numbers fallback) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded (SharedWordWitness221.seeded base numbers fallback)) 15 :=
 CandidateMerkleMeaning261.output_seeded _ ((SharedWordWitness221.seeded_fixed base numbers fallback).1.trans one)
theorem shared (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1)
 (first : numbers 9059%2=numbers 9061%2)
 (second : numbers 10591%2=numbers 10593%2)
 (third : numbers 20935%2=numbers 20937%2)
 (bounded : ∀ entry∈CapturedWordRoot213.words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈CapturedWordRoot213.words,SharedWordWitness221.seeded base numbers fallback entry.1.value=(numbers entry.1.value : F)) :
 CompilerArithmeticBlock44.SatisfiesAt (SharedWordWitness221.completed base numbers fallback) CapturedFullArithmetic52.rowAt 177954 ∧
 (∀ slot∈CapturedBooleanRoot209.slots,∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (SharedWordWitness221.completed base numbers fallback) row.a) (eval (SharedWordWitness221.completed base numbers fallback) row.b)) ∧
 (∀ entry∈CapturedWordRoot213.words,∃ row,CapturedFullRelation58.rowAt (177954+entry.1.position)=some row ∧
 Square (eval (SharedWordWitness221.completed base numbers fallback) row.a) (eval (SharedWordWitness221.completed base numbers fallback) row.b)) ∧
 eval (SharedWordWitness221.completed base numbers fallback) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded (SharedWordWitness221.seeded base numbers fallback)) 15 :=
 ⟨SharedWordWitness221.arithmetic base numbers fallback,
  SharedWordWitness221.boolean_rows base numbers fallback,
  SharedWordWitness221.word_rows base numbers fallback
    (CapturedWordCompatibility251.coherent numbers first second third) bounded meanings,
  path base numbers fallback one⟩
end ShielddSecurity.SharedMerkleWitness263

set_option pp.all true in
#check @ShielddSecurity.SharedMerkleWitness263.path
#print axioms ShielddSecurity.SharedMerkleWitness263.path
set_option pp.all true in
#check @ShielddSecurity.SharedMerkleWitness263.shared
#print axioms ShielddSecurity.SharedMerkleWitness263.shared
