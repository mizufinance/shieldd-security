import ShielddSecurity.ScalarReductionSeed
import ShielddSecurity.PoseidonCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.ScalarReductionFrame

variable {F : Type} [Field F]

/-- A finite write exclusion combines the operand seed, two bit patches and
product materializations. It says nothing about the values of earlier rows. -/
theorem column (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (column : Nat)
    (seedOutside : column ∉ [qColumn,rColumn])
    (qOutside : column < qStart ∨ qStart+4 ≤ column)
    (rOutside : column < rStart ∨ rStart+252 ≤ column)
    (productsOutside : column ∉ PoseidonCompletion.writes stages) :
    CompilerCompletion.run (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart)
      stages column = base column :=
  (PoseidonCompletion.run_outside _ stages column productsOutside).trans
    (ScalarReductionSeed.bitBase_preserves base codec value qColumn rColumn qStart rStart column
      seedOutside qOutside rOutside)

/-- Only preservation uses earlier row truth. A concrete join supplies that
truth from the independent hash constructor, never from its input witness. -/
theorem rows (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (earlier : List Row)
    (constructedEarlier : Satisfies base earlier)
    (outside : ∀ row ∈ earlier, ∀ term ∈ row.a ++ row.b,
      term.1 ∉ [qColumn,rColumn] ∧ (term.1 < qStart ∨ qStart+4 ≤ term.1) ∧
      (term.1 < rStart ∨ rStart+252 ≤ term.1) ∧ term.1 ∉ PoseidonCompletion.writes stages) :
    Satisfies (CompilerCompletion.run
      (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages) earlier := by
  intro row member
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (CompilerCompletion.run
        (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages) terms =
        eval base terms := by
    apply eval_agrees
    intro term present
    obtain ⟨seedOutside,qOutside,rOutside,productsOutside⟩ := outside row member term (inside term present)
    exact column base codec value qColumn rColumn qStart rStart stages term.1
      seedOutside qOutside rOutside productsOutside
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact constructedEarlier row member

set_option pp.all true in
#check @column
#print axioms column
set_option pp.all true in
#check @rows
#print axioms rows

end ShielddSecurity.ScalarReductionFrame
