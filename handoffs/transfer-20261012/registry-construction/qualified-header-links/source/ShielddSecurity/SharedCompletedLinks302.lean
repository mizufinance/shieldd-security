import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.CapturedAssertionLinks57
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedCompletedLinks302
open Compiler CompilerVerifierLinks53 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]

theorem candidate_public (base : Nat → F) :
    ∃ row, CapturedFullRelation58.rowAt 200767 = some row ∧
      Square (eval (CapturedFullRelation58.candidate base) row.a)
        (eval (CapturedFullRelation58.candidate base) row.b) := by
  refine ⟨linkRow 1 22737, ?_, (link_iff _ 1 22737).mpr (CapturedFullRelation58.candidate_links base).1⟩
  rw [show (200767 : Nat) = 177954 + 22813 by decide,
    CapturedFullRelation58.assertion_position 22813 (by decide)]
  exact CapturedAssertionLinks57.public_row

theorem candidate_committed (base : Nat → F) :
    ∃ row, CapturedFullRelation58.rowAt 200768 = some row ∧
      Square (eval (CapturedFullRelation58.candidate base) row.a)
        (eval (CapturedFullRelation58.candidate base) row.b) := by
  refine ⟨linkRow 2 9, ?_, (link_iff _ 2 9).mpr (CapturedFullRelation58.candidate_links base).2.1⟩
  rw [show (200768 : Nat) = 177954 + 22814 by decide,
    CapturedFullRelation58.assertion_position 22814 (by decide)]
  exact CapturedAssertionLinks57.committed_row

theorem candidate_copy (base : Nat → F) :
    ∃ row, CapturedFullRelation58.rowAt 200769 = some row ∧
      Square (eval (CapturedFullRelation58.candidate base) row.a)
        (eval (CapturedFullRelation58.candidate base) row.b) := by
  refine ⟨linkRow 0 copy, ?_, (link_iff _ 0 copy).mpr (CapturedFullRelation58.candidate_links base).2.2.symm⟩
  rw [show (200769 : Nat) = 177954 + 22815 by decide,
    CapturedFullRelation58.assertion_position 22815 (by decide)]
  exact CapturedAssertionLinks57.copy_row

theorem shared_public (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    ∃ row, CapturedFullRelation58.rowAt 200767 = some row ∧
      Square (eval (SharedWordWitness221.completed base numbers fallback) row.a)
        (eval (SharedWordWitness221.completed base numbers fallback) row.b) :=
  candidate_public (SharedWordWitness221.seeded base numbers fallback)

theorem shared_committed (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    ∃ row, CapturedFullRelation58.rowAt 200768 = some row ∧
      Square (eval (SharedWordWitness221.completed base numbers fallback) row.a)
        (eval (SharedWordWitness221.completed base numbers fallback) row.b) :=
  candidate_committed (SharedWordWitness221.seeded base numbers fallback)

theorem shared_copy (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    ∃ row, CapturedFullRelation58.rowAt 200769 = some row ∧
      Square (eval (SharedWordWitness221.completed base numbers fallback) row.a)
        (eval (SharedWordWitness221.completed base numbers fallback) row.b) :=
  candidate_copy (SharedWordWitness221.seeded base numbers fallback)
end ShielddSecurity.SharedCompletedLinks302


set_option pp.all true in
#check @ShielddSecurity.SharedCompletedLinks302.candidate_public
#print axioms ShielddSecurity.SharedCompletedLinks302.candidate_public

set_option pp.all true in
#check @ShielddSecurity.SharedCompletedLinks302.candidate_committed
#print axioms ShielddSecurity.SharedCompletedLinks302.candidate_committed

set_option pp.all true in
#check @ShielddSecurity.SharedCompletedLinks302.candidate_copy
#print axioms ShielddSecurity.SharedCompletedLinks302.candidate_copy

set_option pp.all true in
#check @ShielddSecurity.SharedCompletedLinks302.shared_public
#print axioms ShielddSecurity.SharedCompletedLinks302.shared_public

set_option pp.all true in
#check @ShielddSecurity.SharedCompletedLinks302.shared_committed
#print axioms ShielddSecurity.SharedCompletedLinks302.shared_committed

set_option pp.all true in
#check @ShielddSecurity.SharedCompletedLinks302.shared_copy
#print axioms ShielddSecurity.SharedCompletedLinks302.shared_copy
