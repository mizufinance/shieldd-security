"""Constructive original EPK publication join using separately audited row frames."""
from .generate_hash_round import _signature_audits


def generate():
    name = 'TransferEpkScope0Completion'
    frames = [f'RuntimeTransferEpk0PublicationFrameCanonicalPart{i:02d}' for i in range(16)]
    frames += ['RuntimeTransferEpk0PublicationFrameCanonicalTail', 'RuntimeTransferEpk0PublicationFrameFirst']
    frames += [f'RuntimeTransferEpk0PublicationFramePage{i:02d}' for i in range(8)]
    text = ''.join(f'import ShielddSecurity.{dep}\n' for dep in ['TransferEpkScope0Relation', 'TransferEpkScope1Relation', 'GroupNativeGenerator', *frames])
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

variable {{F : Type}} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

def groupConstruct (rho : Nat → F) (n : Nat) : Nat → F :=
  RuntimeTransferEpk0FixedTemplateCanonicalPreservation.construct rho n

theorem group_preserves (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (column : Nat)
    (canonicalKept : column ∈ RuntimeTransferEpk0CanonicalOrder.kept)
    (prefixKept : column ∈ RuntimeTransferEpk0FixedWindow000TemplatePrefix.kept)
    (ordinaryKept : column ∈ RuntimeTransferEpk0FixedTemplateOrdinaryTrace.kept) :
    groupConstruct rho n column = rho column := by
  let initial := RuntimeTransferEpk0CanonicalCompletion.construct rho n
  let prefixProgram := RuntimeTransferEpk0FixedWindow000TemplatePrefix.program
    ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)
  have scalarDone := RuntimeTransferEpk0CanonicalCompletion.constructs rho n canonical meaning one four
  have scalarPreserved : initial column = rho column := scalarDone.2.2.2 column canonicalKept
  have prefixProtected := RuntimeTransferEpk0FixedWindow000TemplatePrefix.caller_protected
    ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)
  have prefixPreserved : prefixProgram.build initial column = initial column :=
    GroupCircuitOrder.run_outside initial prefixProgram.stages column
      (fun stage member => prefixProtected stage member column prefixKept)
  have ordinaryPreserved := GroupFixedCircuitCompletion.run_preserves (prefixProgram.build initial)
    ((RuntimeTransferEpk0FixedTemplateOrdinaryTrace.windows n).map GroupFixedTemplateTrace.Window.program)
    RuntimeTransferEpk0FixedTemplateOrdinaryTrace.kept
    (RuntimeTransferEpk0FixedTemplateOrdinaryTrace.caller_protected n) column ordinaryKept
  exact ordinaryPreserved.trans (prefixPreserved.trans scalarPreserved)

def publicationBlocks : List (List Row) := [{','.join(frame+'.rows' for frame in frames)}]

private theorem publication_blocks_rows : publicationBlocks.flatten = TransferEpkCanonicalFixedRelation.rows := by
  rw [TransferEpkCanonicalFixedRelation.rows,TransferEpkScope1Relation.source_fixed_rows]
  simp only [publicationBlocks,List.flatten_cons,List.flatten_nil,List.append_nil,
    {','.join(frame+'.rows' for frame in frames)},
    RuntimeTransferEpk0Canonical.originalRows,RuntimeTransferEpk0Canonical.originalBlocks,
    TransferEpkScope1Relation.sourceBlocks,List.append_assoc]

theorem publication_preserves_relation (rho : Nat → F)
    (satisfied : Satisfies rho TransferEpkCanonicalFixedRelation.rows) :
    Satisfies (RuntimeTransferEpk0CapturedPublication.construct rho) TransferEpkCanonicalFixedRelation.rows := by
  rw [← publication_blocks_rows] at satisfied ⊢
  have each (block : List Row) (member : block ∈ publicationBlocks) :
      Satisfies (RuntimeTransferEpk0CapturedPublication.construct rho) block := by
    have original : Satisfies rho block := by
      intro row present
      exact satisfied row (List.mem_flatten.mpr ⟨block,member,present⟩)
    simp only [publicationBlocks,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in frames)}
'''
    for frame in frames:
        text += f'    · exact {frame}.preserves rho original\n'
    text += '''  intro row member
  obtain ⟨block,present,inside⟩ := List.mem_flatten.mp member
  exact each block present row inside

def construct (rho : Nat → F) (n : Nat) : Nat → F :=
  RuntimeTransferEpk0CapturedPublication.construct (groupConstruct rho n)

theorem complete {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (exactOrder : addOrderOf generator = Scalar.order)
    (positive : 0 < n) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator) :
    Satisfies (construct rho n) TransferEpkScope0Relation.rows ∧ construct rho n 4930 = (n : F) ∧
      (⟨construct rho n 4922,construct rho n 4923⟩ : Group.Point F) = model.coordinates (n • generator) := by
  have completed := TransferEpkCanonicalFixedRelation.complete model rho n generator canonical meaning one linked
    four imaginary nonSquare imaginarySquare baseMeaning
  have point : (⟨groupConstruct rho n 5433,groupConstruct rho n 5434⟩ : Group.Point F) =
      model.coordinates (n • generator) := by
    have endpoint := completed.2
    change (⟨eval (groupConstruct rho n) [(5433,1)],eval (groupConstruct rho n) [(5434,1)]⟩ : Group.Point F) = _ at endpoint
    simpa only [eval,Int.cast_one,one_mul,add_zero] using endpoint
  have unit := group_preserves rho n canonical meaning one four 0 (by decide) (by decide) (by decide)
  have canonicalCopy : 200692 ∈ RuntimeTransferEpk0CanonicalOrder.kept := by
    simp only [RuntimeTransferEpk0CanonicalOrder.kept,List.mem_append]
    right;right;right;right;right;right;right;right
    right;right;right;right;right;right;right;right
    exact (by decide : 200692 ∈ RuntimeTransferEpk0CanonicalOrder.keptPart016)
  have copy := group_preserves rho n canonical meaning one four 200692 canonicalCopy (by decide) (by decide)
  have scalarKept := group_preserves rho n canonical meaning one four 4930 (by decide) (by decide) (by decide)
  have inverse := GroupNativeGenerator.canonical_multiple_inverse _ model generator exactOrder n positive canonical
  have legal : groupConstruct rho n 5433 ≠ 0 := by
    have x := congrArg Group.Point.x point
    rw [← x] at inverse
    intro zero
    have impossible : (0 : F) = 1 := by simpa only [zero,zero_mul] using inverse
    exact zero_ne_one impossible
  have publication := RuntimeTransferEpk0CapturedPublication.complete (groupConstruct rho n)
    (unit.trans one) (by rw [copy,unit,linked]) legal
  have allRows : Satisfies (construct rho n) TransferEpkScope0Relation.rows := by
    intro row member
    rcases List.mem_append.mp member with groupMember | publicationMember
    · exact publication_preserves_relation (groupConstruct rho n) completed.1 row groupMember
    · exact publication row publicationMember
  have bindings := RuntimeTransferEpk0CapturedPublication.publication_sound (construct rho n) publication
  have xKept := RuntimeTransferEpk0CapturedPublication.preserves (groupConstruct rho n) 5433 (by decide)
  have yKept := RuntimeTransferEpk0CapturedPublication.preserves (groupConstruct rho n) 5434 (by decide)
  refine ⟨allRows,?_,?_⟩
  · exact (RuntimeTransferEpk0CapturedPublication.preserves (groupConstruct rho n) 4930 (by decide)).trans
      (scalarKept.trans meaning)
  · rw [← bindings.1,← bindings.2.1]
    simpa only [construct,xKept,yKept] using point

#print axioms group_preserves
#print axioms publication_preserves_relation
#print axioms complete
end ShielddSecurity.TransferEpkScope0Completion
'''
    return name, _signature_audits(text)
