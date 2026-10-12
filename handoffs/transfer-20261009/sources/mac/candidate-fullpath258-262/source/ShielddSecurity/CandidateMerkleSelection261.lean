import ShielddSecurity.CapturedMerkleFirstSelection186
import ShielddSecurity.CapturedArithmeticSelection252
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateMerkleSelection261
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) MerkleSelection26Data.originalRows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleFirstSelection186.indices _ CapturedMerkleFirstSelection186.checked
 intro index member
 change index∈List.range' 2722 12++[200769] at member
 rcases List.mem_append.mp member with arithmetic|copying
 · exact CapturedArithmeticSelection252.range_supported 2722 12 (by omega) index arithmetic
 · right
   exact List.mem_singleton.mp copying
end ShielddSecurity.CandidateMerkleSelection261

set_option pp.all true in
#check @ShielddSecurity.CandidateMerkleSelection261.rows
#print axioms ShielddSecurity.CandidateMerkleSelection261.rows
