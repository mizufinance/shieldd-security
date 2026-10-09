import ShielddSecurity.ScalarReductionSeed
import ShielddSecurity.CompilerSupportPreservation

set_option maxHeartbeats 200000

namespace ShielddSecurity.ScalarReductionSupport

variable {F : Type} [Field F]

private theorem quotient_boolean_member (qColumn rColumn qStart rStart column : Nat)
    (member : column ∈ List.range' qStart 4) :
    booleanRow column ∈ ScalarReductionSeed.initialRows qColumn rColumn qStart rStart :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨column,member,rfl⟩))

private theorem remainder_boolean_member (qColumn rColumn qStart rStart column : Nat)
    (member : column ∈ List.range' rStart 252) :
    booleanRow column ∈ ScalarReductionSeed.initialRows qColumn rColumn qStart rStart :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨column,member,rfl⟩))

/-- Initial Boolean rows already make bit columns part of the preserved
support. This proof does not recheck252 membership queries in a giant list. -/
theorem written_quotient_bits (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (kept : List Nat)
    (ordered : CompilerCompletion.Topological kept
      (ScalarReductionSeed.initialRows qColumn rColumn qStart rStart) stages)
    (outside : ∀ column ∈ List.range' qStart 4, column < rStart ∨ rStart+252 ≤ column) :
    ∀ column ∈ List.range' qStart 4,
      CompilerCompletion.run (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages column =
        writeBits (ScalarReductionSeed.seed base codec value qColumn rColumn) qStart
          (encodeBits 4 (ScalarReductionSeed.quotient codec value)) column := by
  intro column member
  have preserved := CompilerSupportPreservation.run_support
    (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages kept _ ordered
    (booleanRow column) (quotient_boolean_member qColumn rColumn qStart rStart column member)
    (column,1) (by simp [booleanRow])
  rw [preserved]
  exact writeBits_preserves _ rStart (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column
    (by simpa only [encodeBits_length] using outside column member)

theorem written_remainder_bits (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (kept : List Nat)
    (ordered : CompilerCompletion.Topological kept
      (ScalarReductionSeed.initialRows qColumn rColumn qStart rStart) stages) :
    ∀ column ∈ List.range' rStart 252,
      CompilerCompletion.run (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages column =
        writeBits (writeBits (ScalarReductionSeed.seed base codec value qColumn rColumn) qStart
          (encodeBits 4 (ScalarReductionSeed.quotient codec value))) rStart
          (encodeBits 252 (ScalarReductionSeed.remainder codec value)) column := by
  intro column member
  exact CompilerSupportPreservation.run_support
    (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages kept _ ordered
    (booleanRow column) (remainder_boolean_member qColumn rColumn qStart rStart column member)
    (column,1) (by simp [booleanRow])

theorem kept_column (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (kept : List Nat)
    (ordered : CompilerCompletion.Topological kept
      (ScalarReductionSeed.initialRows qColumn rColumn qStart rStart) stages)
    (column : Nat) (member : column ∈ kept)
    (seedOutside : column ∉ [qColumn,rColumn])
    (qOutside : column < qStart ∨ qStart+4 ≤ column)
    (rOutside : column < rStart ∨ rStart+252 ≤ column) :
    CompilerCompletion.run (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages column =
      base column :=
  (CompilerCompletion.run_preserves _ stages kept _ ordered column member).trans
    (ScalarReductionSeed.bitBase_preserves base codec value qColumn rColumn qStart rStart column
      seedOutside qOutside rOutside)

/-- The computed hash's actual LC is preserved by independent read support,
so the Euclidean seed remains a reduction of the constructed earlier hash. -/
theorem hash_preserved (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (kept : List Nat)
    (ordered : CompilerCompletion.Topological kept
      (ScalarReductionSeed.initialRows qColumn rColumn qStart rStart) stages)
    (hash : Linear)
    (outside : ∀ term ∈ hash, term.1 ∈ kept ∧ term.1 ∉ [qColumn,rColumn] ∧
      (term.1 < qStart ∨ qStart+4 ≤ term.1) ∧ (term.1 < rStart ∨ rStart+252 ≤ term.1)) :
    eval (CompilerCompletion.run
      (ScalarReductionSeed.bitBase base codec value qColumn rColumn qStart rStart) stages) hash = eval base hash := by
  apply eval_agrees
  intro term member
  obtain ⟨keptMember,seedOutside,qOutside,rOutside⟩ := outside term member
  exact kept_column base codec value qColumn rColumn qStart rStart stages kept ordered term.1
    keptMember seedOutside qOutside rOutside

set_option pp.all true in
#check @written_quotient_bits
#print axioms written_quotient_bits
set_option pp.all true in
#check @written_remainder_bits
#print axioms written_remainder_bits
set_option pp.all true in
#check @kept_column
#print axioms kept_column
set_option pp.all true in
#check @hash_preserved
#print axioms hash_preserved

end ShielddSecurity.ScalarReductionSupport
