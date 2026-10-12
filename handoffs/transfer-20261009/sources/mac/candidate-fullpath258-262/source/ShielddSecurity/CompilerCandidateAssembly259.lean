import ShielddSecurity.CapturedArithmeticSelection252
import ShielddSecurity.CapturedCollectionCandidate256
import ShielddSecurity.CapturedPackedCandidate257
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerCandidateAssembly259
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
theorem append_rows (rho : Nat → F) (left right : List Row)
 (a : Satisfies rho left) (b : Satisfies rho right) : Satisfies rho (left++right) :=
 fun row member => (List.mem_append.mp member).elim (a row) (b row)
variable [CharP F p]
theorem copy_stream (base : Nat → F) (target : Row)
 (checked : CompilerIndexedCopyStream171.rowCheck p copy CapturedFullRelation58.rowAt 200770 200769 target=true) :
 Satisfies (CapturedFullRelation58.candidate base) [target] := by
 apply CapturedArithmeticSelection252.candidate_rows base [200769] [target]
 · exact Bool.and_eq_true_iff.mpr ⟨checked,rfl⟩
 · exact CapturedArithmeticSelection252.copies_supported 1
theorem copy_collection (base : Nat → F) (target : Row)
 (checked : CompilerIndexedCopyCollection174.rowCheck copy CapturedFullRelation58.rowAt 200770 200769 target=true) :
 Satisfies (CapturedFullRelation58.candidate base) [target] := by
 apply CapturedCollectionCandidate256.rows base [200769] [target]
 · exact Bool.and_eq_true_iff.mpr ⟨checked,rfl⟩
 · exact CapturedArithmeticSelection252.copies_supported 1
theorem copy_packed (base : Nat → F) (target : Row)
 (checked : CompilerIndexedCopyConstant178.rowCheck copy CapturedFullRelation58.rowAt 200770 200769 target=true) :
 Satisfies (CapturedFullRelation58.candidate base) [target] := by
 apply CapturedPackedCandidate257.rows base [200769] [target]
 · exact Bool.and_eq_true_iff.mpr ⟨checked,rfl⟩
 · exact CapturedArithmeticSelection252.copies_supported 1
end ShielddSecurity.CompilerCandidateAssembly259

set_option pp.all true in
#check @ShielddSecurity.CompilerCandidateAssembly259.append_rows
#print axioms ShielddSecurity.CompilerCandidateAssembly259.append_rows
set_option pp.all true in
#check @ShielddSecurity.CompilerCandidateAssembly259.copy_stream
#print axioms ShielddSecurity.CompilerCandidateAssembly259.copy_stream
set_option pp.all true in
#check @ShielddSecurity.CompilerCandidateAssembly259.copy_collection
#print axioms ShielddSecurity.CompilerCandidateAssembly259.copy_collection
set_option pp.all true in
#check @ShielddSecurity.CompilerCandidateAssembly259.copy_packed
#print axioms ShielddSecurity.CompilerCandidateAssembly259.copy_packed
