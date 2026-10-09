import ShielddSecurity.ScalarReductionCompletion
import ShielddSecurity.ScalarConstructedBits

set_option maxHeartbeats 300000

namespace ShielddSecurity.ScalarReductionSeed

variable {F : Type} [Field F]

def quotient (codec : TransferReduction.CanonicalField F) (value : F) : Nat :=
  codec.decode value / Scalar.order

def remainder (codec : TransferReduction.CanonicalField F) (value : F) : Nat :=
  codec.decode value % Scalar.order

def seed (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn : Nat) : Nat → F :=
  patchAssignment base (fun column => if column = qColumn then (quotient codec value : F)
    else (remainder codec value : F)) [qColumn,rColumn]

theorem seed_operands (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn : Nat) (distinct : qColumn ≠ rColumn) :
    seed base codec value qColumn rColumn qColumn = (quotient codec value : F) ∧
      seed base codec value qColumn rColumn rColumn = (remainder codec value : F) ∧
      seed base codec value qColumn rColumn qColumn * (Scalar.order : F) +
        seed base codec value qColumn rColumn rColumn = value := by
  have qValue : seed base codec value qColumn rColumn qColumn = (quotient codec value : F) := by
    simp [seed,patchAssignment]
  have rValue : seed base codec value qColumn rColumn rColumn = (remainder codec value : F) := by
    simp [seed,patchAssignment,Ne.symm distinct]
  exact ⟨qValue,rValue,by rw [qValue,rValue]; exact (ScalarReductionCompletion.decoded_operands codec value).2.2.2⟩

theorem seed_preserves (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn column : Nat) (outside : column ∉ [qColumn,rColumn]) :
    seed base codec value qColumn rColumn column = base column :=
  patchAssignment_preserves base _ _ column outside

def bitBase (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) : Nat → F :=
  writeBits (writeBits (seed base codec value qColumn rColumn) qStart (encodeBits 4 (quotient codec value)))
    rStart (encodeBits 252 (remainder codec value))

def initialRows (qColumn rColumn qStart rStart : Nat) : List Row :=
  ScalarComparatorCompletion.initialRows qColumn qStart 4 ++
    ScalarComparatorCompletion.initialRows rColumn rStart 252

/-- Both bit blocks and both reconstruction rows are constructed before any
comparator products. The quotient/remainder values come from the global codec.
The footprint premises are finite allocation certificates, never row truth. -/
theorem initializes (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (distinct : qColumn ≠ rColumn)
    (qOutside : qColumn < qStart ∨ qStart + 4 ≤ qColumn)
    (rOutsideQ : rColumn < qStart ∨ qStart + 4 ≤ rColumn)
    (rOutside : rColumn < rStart ∨ rStart + 252 ≤ rColumn)
    (qRowsOutside : ∀ row ∈ ScalarComparatorCompletion.initialRows qColumn qStart 4,
      ∀ term ∈ row.a ++ row.b, term.1 < rStart ∨ rStart + 252 ≤ term.1) :
    Satisfies (bitBase base codec value qColumn rColumn qStart rStart)
      (initialRows qColumn rColumn qStart rStart) := by
  let seeded := seed base codec value qColumn rColumn
  let qBits := writeBits seeded qStart (encodeBits 4 (quotient codec value))
  have operands := seed_operands base codec value qColumn rColumn distinct
  have bounds := ScalarReductionCompletion.decoded_operands codec value
  have qBound : quotient codec value < 2^4 := by
    have small : quotient codec value ≤ 8 := bounds.1
    omega
  have rBound : remainder codec value < 2^252 :=
    bounds.2.1.trans (by decide : Scalar.order < 2^252)
  have qDone : Satisfies qBits (ScalarComparatorCompletion.initialRows qColumn qStart 4) :=
    writeBits_range_complete seeded qColumn qStart 4 (quotient codec value) qBound operands.1 qOutside
  have rMeaning : qBits rColumn = (remainder codec value : F) := by
    exact (writeBits_preserves seeded qStart (encodeBits 4 (quotient codec value)) rColumn
      (by simpa only [encodeBits_length] using rOutsideQ)).trans operands.2.1
  have rDone : Satisfies (writeBits qBits rStart (encodeBits 252 (remainder codec value)))
      (ScalarComparatorCompletion.initialRows rColumn rStart 252) :=
    writeBits_range_complete qBits rColumn rStart 252 (remainder codec value) rBound rMeaning rOutside
  intro row member
  rcases List.mem_append.mp member with qRow | rRow
  · have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval (bitBase base codec value qColumn rColumn qStart rStart) terms = eval qBits terms := by
      apply eval_agrees
      intro term present
      exact writeBits_preserves qBits rStart (encodeBits 252 (remainder codec value)) term.1
        (by simpa only [encodeBits_length] using qRowsOutside row qRow term (included term present))
    rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
      agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
    exact qDone row qRow
  · exact rDone row rRow

theorem bitBase_preserves (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart column : Nat)
    (seedOutside : column ∉ [qColumn,rColumn])
    (qOutside : column < qStart ∨ qStart + 4 ≤ column)
    (rOutside : column < rStart ∨ rStart + 252 ≤ column) :
    bitBase base codec value qColumn rColumn qStart rStart column = base column := by
  rw [bitBase,writeBits_preserves _ rStart _ column (by simpa only [encodeBits_length] using rOutside),
    writeBits_preserves _ qStart _ column (by simpa only [encodeBits_length] using qOutside),
    seed_preserves base codec value qColumn rColumn column seedOutside]

theorem products_constructed (base : Nat → F) (codec : TransferReduction.CanonicalField F) (value : F)
    (qColumn rColumn qStart rStart : Nat) (stages : List CompilerCompletion.Step) (kept : List Nat)
    (distinct : qColumn ≠ rColumn)
    (qOutside : qColumn < qStart ∨ qStart + 4 ≤ qColumn)
    (rOutsideQ : rColumn < qStart ∨ qStart + 4 ≤ rColumn)
    (rOutside : rColumn < rStart ∨ rStart + 252 ≤ rColumn)
    (qRowsOutside : ∀ row ∈ ScalarComparatorCompletion.initialRows qColumn qStart 4,
      ∀ term ∈ row.a ++ row.b, term.1 < rStart ∨ rStart + 252 ≤ term.1)
    (ordered : CompilerCompletion.Topological kept (initialRows qColumn rColumn qStart rStart) stages)
    (products : ScalarRandomizerCompletion.Products stages) :
    Satisfies (CompilerCompletion.run (bitBase base codec value qColumn rColumn qStart rStart) stages)
      (initialRows qColumn rColumn qStart rStart ++ CompilerCompletion.emitted stages) :=
  CompilerCompletion.run_complete _ stages kept _ ordered
    (ScalarRandomizerCompletion.products_legal _ stages products)
    (initializes base codec value qColumn rColumn qStart rStart distinct qOutside rOutsideQ rOutside qRowsOutside)

set_option pp.all true in
#check @seed_operands
#print axioms seed_operands
set_option pp.all true in
#check @seed_preserves
#print axioms seed_preserves
set_option pp.all true in
#check @initializes
#print axioms initializes
set_option pp.all true in
#check @bitBase_preserves
#print axioms bitBase_preserves
set_option pp.all true in
#check @products_constructed
#print axioms products_constructed

end ShielddSecurity.ScalarReductionSeed
