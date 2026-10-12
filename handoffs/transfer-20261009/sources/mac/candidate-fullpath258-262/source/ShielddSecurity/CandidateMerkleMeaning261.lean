import ShielddSecurity.CandidateMerklePrior261
import ShielddSecurity.CandidateFirstMerkleRows259
import ShielddSecurity.CandidateMerkleRest261
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateMerkleMeaning261
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem output (base : Nat → F) (one : base 0=1) :
 eval (CapturedFullRelation58.candidate base) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CapturedFullRelation58.candidate base) 15 :=
 MerklePath33Meaning.arbitrary _ (MerkleArithmeticConstruction253.candidate_zero base one)
   (CandidateMerklePrior261.rows base) (CandidateFirstMerkleRows259.rows base) (CandidateMerkleRest261.rows base)
omit [CharP F p] in
theorem input_frame (base : Nat → F) (column : Nat) (below : column<22738) :
 CapturedFullRelation58.candidate base column=CompilerVerifierLinks53.seeded base column :=
 CapturedFullArithmetic52.outside _ column (Or.inl below)
omit [CharP F p] in
theorem meaning_seeded (base : Nat → F) :
 MerklePath33Meaning.meaning (CapturedFullRelation58.candidate base) 15=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded base) 15 :=
 MerklePath33Meaning.meaning_agrees _ _ (input_frame base) 15
theorem output_seeded (base : Nat → F) (one : base 0=1) :
 eval (CapturedFullRelation58.candidate base) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded base) 15 :=
 (output base one).trans (meaning_seeded base)
end ShielddSecurity.CandidateMerkleMeaning261

set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleMeaning261.output
#print axioms ShielddSecurity.CandidateMerkleMeaning261.output
set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleMeaning261.input_frame
#print axioms ShielddSecurity.CandidateMerkleMeaning261.input_frame
set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleMeaning261.meaning_seeded
#print axioms ShielddSecurity.CandidateMerkleMeaning261.meaning_seeded
set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleMeaning261.output_seeded
#print axioms ShielddSecurity.CandidateMerkleMeaning261.output_seeded
