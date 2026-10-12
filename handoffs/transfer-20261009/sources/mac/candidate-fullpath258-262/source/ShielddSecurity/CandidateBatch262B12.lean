import ShielddSecurity.CapturedMerkleFirstGlobal186B23
import ShielddSecurity.CapturedArithmeticSelection252
import ShielddSecurity.CapturedMerkleFirstGlobal186B24
import ShielddSecurity.CapturedMerkleFirstGlobal186B25
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CandidateRows258P229
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleFirstGlobal186B23.rows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleFirstGlobal186B23.indices CapturedMerkleFirstGlobal186B23.rows CapturedMerkleFirstGlobal186B23.checked
 change ∀ index∈List.range' 3102 16,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 3102 16 (by omega)
end ShielddSecurity.CandidateRows258P229
namespace ShielddSecurity.CandidateRows258P230
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleFirstGlobal186B24.rows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleFirstGlobal186B24.indices CapturedMerkleFirstGlobal186B24.rows CapturedMerkleFirstGlobal186B24.checked
 change ∀ index∈List.range' 3118 16,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 3118 16 (by omega)
end ShielddSecurity.CandidateRows258P230
namespace ShielddSecurity.CandidateRows258P231
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) CapturedMerkleFirstGlobal186B25.rows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleFirstGlobal186B25.indices CapturedMerkleFirstGlobal186B25.rows CapturedMerkleFirstGlobal186B25.checked
 change ∀ index∈List.range' 3134 12,CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported 3134 12 (by omega)
end ShielddSecurity.CandidateRows258P231

set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P229.rows
#print axioms ShielddSecurity.CandidateRows258P229.rows
set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P230.rows
#print axioms ShielddSecurity.CandidateRows258P230.rows
set_option pp.all true in
#check @ShielddSecurity.CandidateRows258P231.rows
#print axioms ShielddSecurity.CandidateRows258P231.rows
