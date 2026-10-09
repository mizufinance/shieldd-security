import ShielddSecurity.TransferEpkScope1Relation
import ShielddSecurity.GroupNativeGenerator
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameFirst
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameCanonicalPart000
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameCanonicalPart001
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameCanonicalPart002
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameCanonicalPart003
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameCanonicalPart004
import ShielddSecurity.RuntimeTransferEpk1PublicationFrameCanonicalPart005
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage00
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage01
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage02
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage03
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage04
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage05
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage06
import ShielddSecurity.RuntimeTransferEpk1PublicationFramePage07

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkScope1Completion

variable {F : Type} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

def groupConstruct (rho : Nat → F) (n : Nat) : Nat → F :=
  fun column => RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct
    (TransferEpkScope1Relation.pullback rho) n (RuntimeTransferEpk1RenamingMap.columns column)

theorem pullback_group (rho : Nat → F) (n : Nat) :
    TransferEpkScope1Relation.pullback (groupConstruct rho n) =
      RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct
        (TransferEpkScope1Relation.pullback rho) n := by
  funext column
  simp only [TransferEpkScope1Relation.pullback,groupConstruct,RuntimeTransferEpk1RenamingMap.inverted]

theorem group_preserves (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 6334 = (n : F)) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (column : Nat)
    (canonicalKept : column ∈ RuntimeTransferEpk0CanonicalOrder.kept)
    (prefixKept : column ∈ RuntimeTransferEpk0FixedWindow000TemplatePrefix.kept)
    (ordinaryKept : column ∈ RuntimeTransferEpk0FixedTemplateOrdinaryTrace.kept) :
    groupConstruct rho n (RuntimeTransferEpk1RenamingMap.columns column) =
      rho (RuntimeTransferEpk1RenamingMap.columns column) := by
  let base := TransferEpkScope1Relation.pullback rho
  let initial := RuntimeTransferEpk0CanonicalCompletion.construct base n
  let prefixProgram := RuntimeTransferEpk0FixedWindow000TemplatePrefix.program
    ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)
  have zeroColumn : RuntimeTransferEpk1RenamingMap.columns 0 = 0 := by decide
  have scalarColumn : RuntimeTransferEpk1RenamingMap.columns 4930 = 6334 := by decide
  have sourceMeaning : base 4930 = (n : F) := by
    simpa only [base,TransferEpkScope1Relation.pullback,scalarColumn] using meaning
  have sourceOne : base 0 = 1 := by
    simpa only [base,TransferEpkScope1Relation.pullback,zeroColumn] using one
  have scalarDone := RuntimeTransferEpk0CanonicalCompletion.constructs base n canonical sourceMeaning sourceOne four
  have scalarPreserved : initial column = base column := scalarDone.2.2.2 column canonicalKept
  have prefixProtected := RuntimeTransferEpk0FixedWindow000TemplatePrefix.caller_protected
    ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)
  have prefixPreserved : prefixProgram.build initial column = initial column :=
    GroupCircuitOrder.run_outside initial prefixProgram.stages column
      (fun stage member => prefixProtected stage member column prefixKept)
  have ordinaryPreserved := GroupFixedCircuitCompletion.run_preserves (prefixProgram.build initial)
    ((RuntimeTransferEpk0FixedTemplateOrdinaryTrace.windows n).map GroupFixedTemplateTrace.Window.program)
    RuntimeTransferEpk0FixedTemplateOrdinaryTrace.kept
    (RuntimeTransferEpk0FixedTemplateOrdinaryTrace.caller_protected n) column ordinaryKept
  change RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct base n
    (RuntimeTransferEpk1RenamingMap.columns (RuntimeTransferEpk1RenamingMap.columns column)) = _
  rw [RuntimeTransferEpk1RenamingMap.inverted]
  exact ordinaryPreserved.trans (prefixPreserved.trans scalarPreserved)

theorem group_complete {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (canonical : n < Scalar.order)
    (meaning : rho 6334 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator) :
    Satisfies (groupConstruct rho n) TransferEpkScope1Relation.relationRows ∧
      (⟨groupConstruct rho n 6837,groupConstruct rho n 6838⟩ : Group.Point F) =
        model.coordinates (n • generator) := by
  have zeroColumn : RuntimeTransferEpk1RenamingMap.columns 0 = 0 := by decide
  have scalarColumn : RuntimeTransferEpk1RenamingMap.columns 4930 = 6334 := by decide
  have copyColumn : RuntimeTransferEpk1RenamingMap.columns 200692 = 200692 := by decide
  have sourceMeaning : TransferEpkScope1Relation.pullback rho 4930 = (n : F) := by
    simpa only [TransferEpkScope1Relation.pullback,scalarColumn] using meaning
  have sourceOne : TransferEpkScope1Relation.pullback rho 0 = 1 := by
    simpa only [TransferEpkScope1Relation.pullback,zeroColumn] using one
  have sourceLinked : TransferEpkScope1Relation.pullback rho 200692 = TransferEpkScope1Relation.pullback rho 0 := by
    simpa only [TransferEpkScope1Relation.pullback,zeroColumn,copyColumn] using linked
  have completed := TransferEpkCanonicalFixedRelation.complete model (TransferEpkScope1Relation.pullback rho)
    n generator canonical sourceMeaning sourceOne sourceLinked four imaginary nonSquare imaginarySquare baseMeaning
  constructor
  · apply (TransferEpkScope1Relation.relation_transport (groupConstruct rho n)).mpr
    simpa only [pullback_group] using completed.1
  · have xInverse : RuntimeTransferEpk1RenamingMap.columns 6837 = 5433 := by decide
    have yInverse : RuntimeTransferEpk1RenamingMap.columns 6838 = 5434 := by decide
    have point := completed.2
    change (⟨eval (RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct
      (TransferEpkScope1Relation.pullback rho) n) [(5433,1)],
      eval (RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct
      (TransferEpkScope1Relation.pullback rho) n) [(5434,1)]⟩ : Group.Point F) = _ at point
    simpa only [groupConstruct,xInverse,yInverse,eval,Int.cast_one,one_mul,add_zero] using point

def publicationBlocks : List (List Row) := [
  RuntimeTransferEpk1PublicationFrameCanonicalPart000.rows,
  RuntimeTransferEpk1PublicationFrameCanonicalPart001.rows,
  RuntimeTransferEpk1PublicationFrameCanonicalPart002.rows,
  RuntimeTransferEpk1PublicationFrameCanonicalPart003.rows,
  RuntimeTransferEpk1PublicationFrameCanonicalPart004.rows,
  RuntimeTransferEpk1PublicationFrameCanonicalPart005.rows,
  RuntimeTransferEpk1PublicationFrameFirst.rows,
  RuntimeTransferEpk1PublicationFramePage00.rows,
  RuntimeTransferEpk1PublicationFramePage01.rows,
  RuntimeTransferEpk1PublicationFramePage02.rows,
  RuntimeTransferEpk1PublicationFramePage03.rows,
  RuntimeTransferEpk1PublicationFramePage04.rows,
  RuntimeTransferEpk1PublicationFramePage05.rows,
  RuntimeTransferEpk1PublicationFramePage06.rows,
  RuntimeTransferEpk1PublicationFramePage07.rows]

private theorem publication_blocks_rows : publicationBlocks.flatten = TransferEpkScope1Relation.relationRows := by
  simp only [publicationBlocks, List.flatten_cons,List.flatten_nil,List.append_nil,
    RuntimeTransferEpk1PublicationFrameCanonicalPart000.rows,
    RuntimeTransferEpk1PublicationFrameCanonicalPart001.rows,
    RuntimeTransferEpk1PublicationFrameCanonicalPart002.rows,
    RuntimeTransferEpk1PublicationFrameCanonicalPart003.rows,
    RuntimeTransferEpk1PublicationFrameCanonicalPart004.rows,
    RuntimeTransferEpk1PublicationFrameCanonicalPart005.rows,
    RuntimeTransferEpk1PublicationFrameFirst.rows,
    RuntimeTransferEpk1PublicationFramePage00.rows,
    RuntimeTransferEpk1PublicationFramePage01.rows,
    RuntimeTransferEpk1PublicationFramePage02.rows,
    RuntimeTransferEpk1PublicationFramePage03.rows,
    RuntimeTransferEpk1PublicationFramePage04.rows,
    RuntimeTransferEpk1PublicationFramePage05.rows,
    RuntimeTransferEpk1PublicationFramePage06.rows,
    RuntimeTransferEpk1PublicationFramePage07.rows,
    TransferEpkScope1Relation.relationRows,TransferEpkScope1Relation.targetBlocks,
    RuntimeTransferEpk1RenamingRows126.rawRows,List.append_assoc]

theorem publication_preserves_relation (rho : Nat → F)
    (satisfied : Satisfies rho TransferEpkScope1Relation.relationRows) :
    Satisfies (RuntimeTransferEpk1CapturedPublication.construct rho)
      TransferEpkScope1Relation.relationRows := by
  rw [← publication_blocks_rows] at satisfied ⊢
  have each (block : List Row) (member : block ∈ publicationBlocks) :
      Satisfies (RuntimeTransferEpk1CapturedPublication.construct rho) block := by
    have original : Satisfies rho block := by
      intro row present
      exact satisfied row (List.mem_flatten.mpr ⟨block,member,present⟩)
    simp only [publicationBlocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact RuntimeTransferEpk1PublicationFrameCanonicalPart000.preserves rho original
    · exact RuntimeTransferEpk1PublicationFrameCanonicalPart001.preserves rho original
    · exact RuntimeTransferEpk1PublicationFrameCanonicalPart002.preserves rho original
    · exact RuntimeTransferEpk1PublicationFrameCanonicalPart003.preserves rho original
    · exact RuntimeTransferEpk1PublicationFrameCanonicalPart004.preserves rho original
    · exact RuntimeTransferEpk1PublicationFrameCanonicalPart005.preserves rho original
    · exact RuntimeTransferEpk1PublicationFrameFirst.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage00.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage01.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage02.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage03.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage04.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage05.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage06.preserves rho original
    · exact RuntimeTransferEpk1PublicationFramePage07.preserves rho original
  intro row member
  obtain ⟨block,present,inside⟩ := List.mem_flatten.mp member
  exact each block present row inside

def construct (rho : Nat → F) (n : Nat) : Nat → F :=
  RuntimeTransferEpk1CapturedPublication.construct (groupConstruct rho n)

theorem complete {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J)
    (exactOrder : addOrderOf generator = Scalar.order)
    (positive : 0 < n) (canonical : n < Scalar.order)
    (meaning : rho 6334 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator) :
    Satisfies (construct rho n) TransferEpkScope1Relation.rows ∧
      construct rho n 6334 = (n : F) ∧
      (⟨construct rho n 6326,construct rho n 6327⟩ : Group.Point F) =
        model.coordinates (n • generator) := by
  have completed := group_complete model rho n generator canonical meaning one linked four
    imaginary nonSquare imaginarySquare baseMeaning
  have unit : groupConstruct rho n 0 = rho 0 := by
    have kept := group_preserves rho n canonical meaning one four 0 (by decide) (by decide) (by decide)
    simpa only [show RuntimeTransferEpk1RenamingMap.columns 0 = 0 from by decide] using kept
  have copy : groupConstruct rho n 200692 = rho 200692 := by
    have canonicalCopy : 200692 ∈ RuntimeTransferEpk0CanonicalOrder.kept := by
      simp only [RuntimeTransferEpk0CanonicalOrder.kept,List.mem_append]
      right;right;right;right;right;right;right;right
      right;right;right;right;right;right;right;right
      exact (by decide : 200692 ∈ RuntimeTransferEpk0CanonicalOrder.keptPart016)
    have kept := group_preserves rho n canonical meaning one four 200692 canonicalCopy (by decide) (by decide)
    simpa only [show RuntimeTransferEpk1RenamingMap.columns 200692 = 200692 from by decide] using kept
  have scalarKept : groupConstruct rho n 6334 = rho 6334 := by
    have kept := group_preserves rho n canonical meaning one four 4930 (by decide) (by decide) (by decide)
    simpa only [show RuntimeTransferEpk1RenamingMap.columns 4930 = 6334 from by decide] using kept
  have inverse := GroupNativeGenerator.canonical_multiple_inverse _ model generator exactOrder n positive canonical
  have legal : groupConstruct rho n 6837 ≠ 0 := by
    have x := congrArg Group.Point.x completed.2
    rw [← x] at inverse
    intro zero
    have impossible : (0 : F) = 1 := by simpa only [zero,zero_mul] using inverse
    exact zero_ne_one impossible
  have publication := RuntimeTransferEpk1CapturedPublication.complete (groupConstruct rho n)
    (unit.trans one) (by rw [copy,unit,linked]) legal
  have allRows : Satisfies (construct rho n) TransferEpkScope1Relation.rows := by
    intro row member
    rcases List.mem_append.mp member with groupMember | publicationMember
    · exact publication_preserves_relation (groupConstruct rho n) completed.1 row groupMember
    · exact publication row publicationMember
  have bindings := RuntimeTransferEpk1CapturedPublication.publication_sound (construct rho n) publication
  have xKept := RuntimeTransferEpk1CapturedPublication.preserves (groupConstruct rho n) 6837 (by decide)
  have yKept := RuntimeTransferEpk1CapturedPublication.preserves (groupConstruct rho n) 6838 (by decide)
  refine ⟨allRows,?_,?_⟩
  · exact (RuntimeTransferEpk1CapturedPublication.preserves (groupConstruct rho n) 6334 (by decide)).trans
      (scalarKept.trans meaning)
  · rw [← bindings.1,← bindings.2.1]
    simpa only [construct,xKept,yKept] using completed.2

set_option pp.all true in
#check @pullback_group
#print axioms pullback_group
set_option pp.all true in
#check @group_preserves
#print axioms group_preserves
set_option pp.all true in
#check @group_complete
#print axioms group_complete
set_option pp.all true in
#check @publication_preserves_relation
#print axioms publication_preserves_relation
set_option pp.all true in
#check @complete
#print axioms complete

end ShielddSecurity.TransferEpkScope1Completion
