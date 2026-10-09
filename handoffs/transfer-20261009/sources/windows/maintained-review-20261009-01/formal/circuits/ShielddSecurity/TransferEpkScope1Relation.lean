import ShielddSecurity.TransferEpkCanonicalFixedRelation
import ShielddSecurity.RuntimeTransferEpk1RenamingRows000
import ShielddSecurity.RuntimeTransferEpk1RenamingRows126
import ShielddSecurity.RuntimeTransferEpk1CapturedPublication
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage00
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage01
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage02
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage03
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage04
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage05
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage06
import ShielddSecurity.RuntimeTransferEpk1TemplateRenamingPage07

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEpkScope1Relation

def pullback {F : Type} (rho : Nat → F) : Nat → F :=
  fun column => rho (RuntimeTransferEpk1RenamingMap.columns column)

def sourceBlocks : List (List Row) := [RuntimeTransferEpk0FixedWindow000.rawRows,
  RuntimeTransferEpk1TemplateRenamingPage00.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage01.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage02.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage03.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage04.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage05.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage06.sourceRows,
  RuntimeTransferEpk1TemplateRenamingPage07.sourceRows]

def targetBlocks : List (List Row) := [RuntimeTransferEpk1RenamingRows000.rawRows,
  RuntimeTransferEpk1TemplateRenamingPage00.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage01.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage02.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage03.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage04.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage05.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage06.targetRows,
  RuntimeTransferEpk1TemplateRenamingPage07.targetRows]

def relationRows : List Row := RuntimeTransferEpk1RenamingRows126.rawRows ++ targetBlocks.flatten
def rows : List Row := relationRows ++ RuntimeTransferEpk1CapturedPublication.rows

noncomputable def scalar {F : Type} [Field F] (rho : Nat → F) : Nat :=
  binary (RuntimeTransferEpk0Canonical.decodedBits (pullback rho))

theorem source_fixed_rows : RuntimeTransferEpk0FixedTemplateScalarSoundness.rows 0 = sourceBlocks.flatten := by
  simp only [RuntimeTransferEpk0FixedTemplateScalarSoundness.rows,
    RuntimeTransferEpk0FixedTemplateOrdinaryTrace.windows,
    TransferEpkFixedRowIdentity.page_rows_flatten,
    RuntimeTransferEpk0FixedTemplateOrdinaryTrace.pages,List.map_cons,List.map_nil]
  rw [← RuntimeTransferEpk1TemplateRenamingPage00.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage01.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage02.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage03.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage04.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage05.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage06.physical_program_rows,
    ← RuntimeTransferEpk1TemplateRenamingPage07.physical_program_rows]
  rfl

variable {F : Type} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

private theorem satisfies_append (rho : Nat → F) (left right : List Row) :
    Satisfies rho (left ++ right) ↔ Satisfies rho left ∧ Satisfies rho right := by
  constructor
  · intro satisfied
    exact ⟨fun row member => satisfied row (List.mem_append_left _ member),
      fun row member => satisfied row (List.mem_append_right _ member)⟩
  · rintro ⟨leftSatisfied,rightSatisfied⟩ row member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact leftSatisfied row leftMember
    · exact rightSatisfied row rightMember

private theorem mapped_iff (rho : Nat → F) (original : List Row) :
    Satisfies rho (original.map (RowRenaming.row RuntimeTransferEpk1RenamingMap.columns)) ↔
      Satisfies (pullback rho) original := by
  constructor
  · intro satisfied
    exact RowRenaming.satisfied_rows rho RuntimeTransferEpk1RenamingMap.columns original _
      (fun item member => List.mem_map.mpr ⟨item,member,rfl⟩) satisfied
  · intro satisfied row member
    obtain ⟨item,present,rfl⟩ := List.mem_map.mp member
    simpa only [RowRenaming.row,RowRenaming.eval_linear,pullback] using satisfied item present

theorem fixed_rows_transport (rho : Nat → F) :
    Satisfies rho targetBlocks.flatten ↔ Satisfies (pullback rho) sourceBlocks.flatten := by
  have first : Satisfies rho RuntimeTransferEpk1RenamingRows000.rawRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk0FixedWindow000.rawRows := by
    rw [RuntimeTransferEpk1RenamingRows000.exact_rows]
    exact mapped_iff rho _
  have page0 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage00.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage00.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage00.sound rho,RuntimeTransferEpk1TemplateRenamingPage00.complete rho⟩)
  have page1 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage01.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage01.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage01.sound rho,RuntimeTransferEpk1TemplateRenamingPage01.complete rho⟩)
  have page2 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage02.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage02.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage02.sound rho,RuntimeTransferEpk1TemplateRenamingPage02.complete rho⟩)
  have page3 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage03.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage03.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage03.sound rho,RuntimeTransferEpk1TemplateRenamingPage03.complete rho⟩)
  have page4 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage04.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage04.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage04.sound rho,RuntimeTransferEpk1TemplateRenamingPage04.complete rho⟩)
  have page5 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage05.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage05.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage05.sound rho,RuntimeTransferEpk1TemplateRenamingPage05.complete rho⟩)
  have page6 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage06.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage06.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage06.sound rho,RuntimeTransferEpk1TemplateRenamingPage06.complete rho⟩)
  have page7 := (show Satisfies rho RuntimeTransferEpk1TemplateRenamingPage07.targetRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk1TemplateRenamingPage07.sourceRows from
    ⟨RuntimeTransferEpk1TemplateRenamingPage07.sound rho,RuntimeTransferEpk1TemplateRenamingPage07.complete rho⟩)
  simp only [targetBlocks,sourceBlocks,List.flatten_cons,List.flatten_nil,List.append_nil,
    satisfies_append,first,page0,page1,page2,page3,page4,page5,page6,page7]

theorem relation_transport (rho : Nat → F) :
    Satisfies rho relationRows ↔ Satisfies (pullback rho) TransferEpkCanonicalFixedRelation.rows := by
  have canonical : Satisfies rho RuntimeTransferEpk1RenamingRows126.rawRows ↔
      Satisfies (pullback rho) RuntimeTransferEpk0Canonical.originalRows := by
    rw [RuntimeTransferEpk1RenamingRows126.exact_rows]
    exact mapped_iff rho _
  rw [relationRows,TransferEpkCanonicalFixedRelation.rows,source_fixed_rows,
    satisfies_append,satisfies_append,canonical,fixed_rows_transport]

theorem sound {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (generator : J) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho rows) :
    0 < scalar rho ∧ scalar rho < Scalar.order ∧ (scalar rho : F) = rho 6334 ∧
      (⟨rho 6326,rho 6327⟩ : Group.Point F) = model.coordinates (scalar rho • generator) := by
  have split := (satisfies_append rho relationRows RuntimeTransferEpk1CapturedPublication.rows).mp satisfied
  have expected := (relation_transport rho).mp split.1
  have zeroColumn : RuntimeTransferEpk1RenamingMap.columns 0 = 0 := by decide
  have scalarColumn : RuntimeTransferEpk1RenamingMap.columns 4930 = 6334 := by decide
  have xColumn : RuntimeTransferEpk1RenamingMap.columns 5433 = 6837 := by decide
  have yColumn : RuntimeTransferEpk1RenamingMap.columns 5434 = 6838 := by decide
  have sourceOne : pullback rho 0 = 1 := by simpa only [pullback,zeroColumn] using one
  have derived := TransferEpkCanonicalFixedRelation.sound model (pullback rho) generator sourceOne four
    imaginary nonSquare imaginarySquare baseMeaning expected
  change scalar rho < Scalar.order ∧ (scalar rho : F) = eval (pullback rho) RuntimeTransferEpk0Canonical.privateValue ∧
    GroupFixedCircuitCompletion.point (pullback rho) TransferEpkCanonicalFixedRelation.endpoint =
      model.coordinates (scalar rho • generator) at derived
  have amount : (scalar rho : F) = rho 6334 := by
    simpa only [RuntimeTransferEpk0Canonical.privateValue,eval,Int.cast_one,one_mul,add_zero,
      pullback,scalarColumn] using derived.2.1
  have endpoint := derived.2.2
  change (⟨eval (pullback rho) [(5433,1)],eval (pullback rho) [(5434,1)]⟩ : Group.Point F) = _ at endpoint
  simp only [eval,Int.cast_one,one_mul,add_zero,pullback,xColumn,yColumn] at endpoint
  have publication := RuntimeTransferEpk1CapturedPublication.publication_sound rho split.2
  have published : (⟨rho 6326,rho 6327⟩ : Group.Point F) = model.coordinates (scalar rho • generator) := by
    rw [← publication.1,← publication.2.1]
    exact endpoint
  have nonzero := (RuntimeTransferEpk1CapturedPublication.inverse_sound rho four one split.2).2
  have positive : 0 < scalar rho := by
    by_contra absent
    have zero : scalar rho = 0 := Nat.eq_zero_of_not_pos absent
    have x := congrArg Group.Point.x published
    simp only [zero,zero_nsmul,model.identity,Group.identityPoint] at x
    exact nonzero x
  exact ⟨positive,derived.1,amount,published⟩

set_option pp.all true in
#check @source_fixed_rows
#print axioms source_fixed_rows
set_option pp.all true in
#check @fixed_rows_transport
#print axioms fixed_rows_transport
set_option pp.all true in
#check @relation_transport
#print axioms relation_transport
set_option pp.all true in
#check @sound
#print axioms sound

end ShielddSecurity.TransferEpkScope1Relation
