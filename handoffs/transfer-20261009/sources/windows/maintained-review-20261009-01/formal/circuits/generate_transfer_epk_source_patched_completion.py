"""Conservative patch of the original EPK constructor on actual captured writes."""
from .generate_hash_round import _signature_audits


def generate():
    name='TransferEpkScope0PatchedCompletion'
    core='TransferEpkScope0Completion';rel='TransferEpkScope0Relation'
    publication='RuntimeTransferEpk0CapturedPublication';tree='RuntimeTransferEpk0ConstructiveWriteTree'
    supports=[f'RuntimeTransferEpk0ConstructiveOwnSupportCanonicalPart{i:02d}' for i in range(16)]
    supports+=['RuntimeTransferEpk0ConstructiveOwnSupportCanonicalTail','RuntimeTransferEpk0ConstructiveOwnSupportFirst']
    supports+=[f'RuntimeTransferEpk0ConstructiveOwnSupportPage{i:02d}' for i in range(8)]
    supports+=['RuntimeTransferEpk0ConstructiveOwnSupportPublication']
    text=''.join(f'import ShielddSecurity.{dep}\n' for dep in [core,*supports])
    text+=f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

variable {{F : Type}} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

def construct (rho : Nat → F) (n : Nat) : Nat → F :=
  FiniteWritePatch.assignment {tree}.tree rho ({core}.construct rho n)

theorem native_inputs_preserved (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    ∀ column ∈ {tree}.inputs,{core}.construct rho n column = rho column := by
  have unit : {core}.construct rho n 0 = rho 0 := by
    rw [{core}.construct,{publication}.preserves _ 0 (by decide)]
    exact {core}.group_preserves rho n canonical meaning one four 0 (by decide) (by decide) (by decide)
  have canonicalCopy : 200692 ∈ RuntimeTransferEpk0CanonicalOrder.kept := by
    simp only [RuntimeTransferEpk0CanonicalOrder.kept,List.mem_append]
    right;right;right;right;right;right;right;right
    right;right;right;right;right;right;right;right
    exact (by decide : 200692 ∈ RuntimeTransferEpk0CanonicalOrder.keptPart016)
  have copy : {core}.construct rho n 200692 = rho 200692 := by
    rw [{core}.construct,{publication}.preserves _ 200692 (by decide)]
    exact {core}.group_preserves rho n canonical meaning one four 200692 canonicalCopy (by decide) (by decide)
  have scalarKept : {core}.construct rho n 4930 = rho 4930 := by
    rw [{core}.construct,{publication}.preserves _ 4930 (by decide)]
    exact {core}.group_preserves rho n canonical meaning one four 4930 (by decide) (by decide) (by decide)
  intro column member
  simp only [{tree}.inputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact unit
  · exact copy
  · exact scalarKept

def ownBlocks : List (List Row) := [{','.join(s+'.rows' for s in supports)}]

private theorem own_blocks_rows : ownBlocks.flatten = {rel}.rows := by
  rw [{rel}.rows,TransferEpkCanonicalFixedRelation.rows,TransferEpkScope1Relation.source_fixed_rows]
  simp only [ownBlocks,List.flatten_cons,List.flatten_nil,List.append_nil,
    {','.join(s+'.rows' for s in supports)},
    RuntimeTransferEpk0Canonical.originalRows,RuntimeTransferEpk0Canonical.originalBlocks,
    TransferEpkScope1Relation.sourceBlocks,List.append_assoc]

private theorem own_support (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    ∀ row ∈ {rel}.rows,∀ term ∈ row.a ++ row.b,
      (FiniteColumnRenaming.lookup {tree}.tree term.1).isSome = true ∨
      rho term.1 = {core}.construct rho n term.1 := by
  have inputs := native_inputs_preserved rho n canonical meaning one four
  have each (block : List Row) (member : block ∈ ownBlocks) :
      ∀ row ∈ block,∀ term ∈ row.a ++ row.b,
        (FiniteColumnRenaming.lookup {tree}.tree term.1).isSome = true ∨ term.1 ∈ {tree}.inputs := by
    simp only [ownBlocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in supports)}
'''
    for support in supports:text+=f'    · exact {support}.support\n'
    text+=f'''  intro row member term present
  rw [← own_blocks_rows] at member
  obtain ⟨block,inside,contained⟩ := List.mem_flatten.mp member
  rcases each block inside row contained term present with selected | input
  · exact Or.inl selected
  · exact Or.inr (inputs term.1 input).symm

theorem complete {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (exactOrder : addOrderOf generator = Scalar.order)
    (positive : 0 < n) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator) :
    Satisfies (construct rho n) {rel}.rows ∧ construct rho n 4930 = (n : F) ∧
      (⟨construct rho n 4922,construct rho n 4923⟩ : Group.Point F) = model.coordinates (n • generator) := by
  have completed := {core}.complete model rho n generator exactOrder positive canonical meaning one linked
    four imaginary nonSquare imaginarySquare baseMeaning
  have rowsDone := FiniteWritePatch.built_rows {tree}.tree rho ({core}.construct rho n)
    {rel}.rows (own_support rho n canonical meaning one four) completed.1
  have scalarKept := FiniteWritePatch.preserves {tree}.tree rho ({core}.construct rho n) 4930 (by decide)
  have x := FiniteWritePatch.at_selected {tree}.tree rho ({core}.construct rho n) 4922 (by decide)
  have y := FiniteWritePatch.at_selected {tree}.tree rho ({core}.construct rho n) 4923 (by decide)
  refine ⟨rowsDone,scalarKept.trans meaning,?_⟩
  simpa only [construct,x,y] using completed.2.2

theorem outside_column (rho : Nat → F) (n : Nat) (column : Nat)
    (outside : FiniteColumnRenaming.lookup {tree}.tree column = none) :
    construct rho n column = rho column :=
  FiniteWritePatch.preserves {tree}.tree rho ({core}.construct rho n) column outside

theorem prior_rows (rho : Nat → F) (n : Nat) (rows : List Row)
    (outside : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup {tree}.tree term.1 = none)
    (satisfied : Satisfies rho rows) : Satisfies (construct rho n) rows :=
  FiniteWritePatch.preserves_rows {tree}.tree rho ({core}.construct rho n) rows outside satisfied

#print axioms native_inputs_preserved
#print axioms complete
#print axioms outside_column
#print axioms prior_rows
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)
