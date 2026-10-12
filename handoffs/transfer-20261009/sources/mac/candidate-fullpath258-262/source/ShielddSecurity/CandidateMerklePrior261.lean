import ShielddSecurity.CandidatePriorRows259
import ShielddSecurity.CandidateThreeCallRows259
import ShielddSecurity.CandidateRegistryRows259
import ShielddSecurity.CandidateMerkleSelection261
import ShielddSecurity.MerkleHash27Whole
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateMerklePrior261
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) MerkleHash27Whole.priorRows := by
 intro row member
 simp only [MerkleHash27Whole.priorRows,List.mem_append] at member
 rcases member with ((before|joined)|registry)|selected
 · exact CandidatePriorRows259.rows base row before
 · exact CandidateThreeCallRows259.rows base row joined
 · exact CandidateRegistryRows259.rows base row registry
 · exact CandidateMerkleSelection261.rows base row selected
end ShielddSecurity.CandidateMerklePrior261

set_option pp.all true in
#check @ShielddSecurity.CandidateMerklePrior261.rows
#print axioms ShielddSecurity.CandidateMerklePrior261.rows
