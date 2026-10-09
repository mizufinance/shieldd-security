"""One inverse-to-hash assignment using existing actual RNK constructors.

This consumer opens no ordinary stream and renders no permutation graph.
Every support exclusion is checked on retained bounded row blocks. Native
input/source and registered-leaf associations remain independent joins.
"""
from . import transfer_rnk_inverse_completion as inverse
from . import transfer_relation as relation
from .generate_transfer_rnk_sparse_sequence import _validate, _native_variables, _native_contracts
from .generate_transfer_ivk_reduction_join import _qualify


def inspect_support(row_blocks, inverse_rows):
    """Check actual prior support against the independently owned hash interval."""
    try:
        if not isinstance(row_blocks,list) or len(row_blocks)!=134:
            raise relation.RelationError('RNK inverse/hash exact134 prior blocks')
        counts=[]
        for rows in [*row_blocks,inverse_rows]:
            if not isinstance(rows,list) or not 0<len(rows)<=512:
                raise relation.RelationError('RNK inverse/hash bounded nonempty prior rows')
            previous=-1
            for row in rows:
                if not isinstance(row,dict) or set(row)!={'row','a','b'}:
                    raise relation.RelationError('RNK inverse/hash exact physical row shape')
                index=relation.natural(row['row'],200770)
                if index<=previous:
                    raise relation.RelationError('RNK inverse/hash ordered distinct physical rows')
                previous=index
                for side in ('a','b'):
                    relation.terms(row[side],262144)
                    if any(60778<=column<=61929 for column,_ in row[side]):
                        raise relation.RelationError('RNK inverse/hash actual prior support overwritten')
            counts.append(len(rows))
        if counts[-1]!=4:
            raise relation.RelationError('RNK inverse/hash exact four inverse rows')
        return counts
    except (KeyError,TypeError,AttributeError,IndexError) as error:
        raise relation.RelationError('RNK inverse/hash typed actual support') from error


def generate(checked, extracted, sequence):
    try:
        return _generate(checked,extracted,sequence)
    except (KeyError,TypeError,AttributeError,IndexError) as error:
        raise relation.RelationError('RNK inverse/hash typed accepted constructor inputs') from error


def _generate(checked, extracted, sequence):
    sequence=_validate(sequence)
    plan=inverse.plan(checked,extracted,sequence)
    if (sequence['domain_size'],sequence['full_rows'],plan['roles']['copy'])!=(262144,200770,200692):
        raise relation.RelationError('RNK inverse/hash exact original relation shape and copy')
    if plan['writes']!=[3765,60776,60777]:
        raise relation.RelationError('RNK inverse/hash exact retained reciprocal writes')
    inspect_support([block['target_rows'] for block in sequence['row_blocks']],plan['rows'])
    fp='RuntimeRnkPreHashFootprint'
    source='import ShielddSecurity.RuntimeRnkNativeInverseCompletion\n'
    source+='import ShielddSecurity.RuntimeRnkHashMeaningCompletion\n'
    source+='set_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n'
    source+=f'namespace ShielddSecurity.{fp}\n'
    for index in range(134):
        block=f'RuntimeRnkSparseBlock{index:03d}'
        source+=f'''private theorem block{index}_outside : ∀ row ∈ {block}.actualRows,
    ∀ term ∈ row.a ++ row.b, term.1 < 60778 ∨ 61929 < term.1 := by
  have checked : {block}.actualRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 < 60778 ∨ 61929 < term.1))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)
'''
    source+='''theorem window_rows_outside : ∀ row ∈ RuntimeRnkNativeCompletion.actualRows,
    ∀ term ∈ row.a ++ row.b, term.1 < 60778 ∨ 61929 < term.1 := by
  intro row member term present
  simp only [RuntimeRnkNativeCompletion.actualRows,List.mem_append] at member
  rcases member with '''+' | '.join('inside' for _ in range(8))+'\n'
    for start in range(0,126,16):
        chunk=f'RuntimeRnkNativeChunk{start:03d}'
        indices=[index for index,role in enumerate(sequence['roles']) if role['chunk']==start]
        source+=f'''  · obtain ⟨block,included,member⟩ := List.mem_flatten.mp inside
    simp only [{chunk}.rowBlocks,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with '''+' | '.join('rfl' for _ in indices)+'\n'
        source+=''.join(f'    · exact block{index}_outside row member term present\n' for index in indices)
    source+='''theorem inverse_rows_outside : ∀ row ∈ RuntimeRnkNativeInverseCompletion.rawRows,
    ∀ term ∈ row.a ++ row.b, term.1 < 60778 ∨ 61929 < term.1 := by
  have checked : RuntimeRnkNativeInverseCompletion.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 < 60778 ∨ 61929 < term.1))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)
#print axioms window_rows_outside
#print axioms inverse_rows_outside
'''
    footprint=_qualify(source+f'end ShielddSecurity.{fp}\n',{})
    name='RuntimeRnkInverseHashCompletion'
    aliases=dict(P=fp,I='RuntimeRnkNativeInverseCompletion',H='RuntimeRnkHashSequenceCompletion',
        M='RuntimeRnkHashMeaningCompletion',K0='RuntimeRnkHashOnly',A='RuntimeRnkSparseAssignment',
        C='RuntimeRnkNativeSource',N='RuntimeOwnershipNativeConstructor',SC='ShielddPointCoordinateSeed',
        W='RuntimeRnkNativeCompletion',G='GroupRnkSparseColumns')
    source=f'import ShielddSecurity.{fp}\nset_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n'
    source+=f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
    protected=[0,10,1512,1513,1520,1521,1528,1980,1981,1993,3007,3008,3763,3764,3766,200692]
    source+=f'def protectedColumns : List Nat := {protected}\n'
    source+=_native_variables()+_native_contracts(200692)
    args='fq fr model upstream backend codec nk x y input scalar base'
    contracts='arithmetic initialHash square primitives one linked accepted'
    curve='four imaginary nonSquare imaginarySquare'
    source+=f'''def completed : Nat → F := H.completed (I.completed {args})
def originalRows : List Row := (W.actualRows ++ I.rawRows) ++ K0.rawRows

theorem protected_columns (column : Nat) (member : column ∈ protectedColumns) :
    completed {args} column = I.completed {args} column := by
  have checked : protectedColumns.all (fun column => decide
    (column < 60778 ∨ 61929 < column)) = true := by decide
  exact H.preserves _ column (of_decide_eq_true (List.all_eq_true.mp checked column member))

include {contracts} in
private theorem constants : I.completed {args} 0 = 1 ∧ I.completed {args} 200692 = 1 := by
  have outside (column : Nat) (independent : column < 3009 ∨ 60775 < column) :
      column ∉ A.writeBlocks.flatten.map G.columns := by
    intro member
    obtain ⟨write,present,equal⟩ := List.mem_map.mp member
    have bounds := G.owned_image_bounds write (A.writes_owned write present)
    rw [equal] at bounds
    omega
  have seeded (column : Nat) (away : column ∉ SC.columns 1520 1521) :
      C.initial fq fr model upstream backend input base column = base column :=
    SC.seed_preserves fq fr (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
      model upstream backend input 1520 1521 base column away
  have before (column : Nat) (member : column ∈ [0,200692]) :
      C.nativePrefix fq fr model upstream backend codec nk x y input base column =
        C.initial fq fr model upstream backend input base column :=
    N.ivk_constants fq backend codec nk x y
      (C.initial fq fr model upstream backend input base) column member
  constructor
  · exact (I.preserves {args} 0 (by decide)).trans
      ((A.protected_columns {args} 0 (outside 0 (by omega))).trans
        ((before 0 (by simp)).trans ((seeded 0 (by decide)).trans one)))
  · exact (I.preserves {args} 200692 (by decide)).trans
      ((A.protected_columns {args} 200692 (outside 200692 (by omega))).trans
        ((before 200692 (by simp)).trans ((seeded 200692 (by decide)).trans (linked.trans one))))

include {contracts} in
theorem window_rows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed {args}) W.actualRows := by
  have done := I.original_window_complete {args} {contracts} imaginary nonSquare imaginarySquare
  intro row member
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (completed {args}) terms = eval (I.completed {args}) terms :=
    H.eval_preserved _ terms (by intro term present; exact P.window_rows_outside row member term (inside term present))
  change Square (eval (completed {args}) row.a) (eval (completed {args}) row.b)
  rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
    agrees row.b (by intro term present; exact List.mem_append_right _ present)]
  exact done row member

variable (standardPrime : Nat.Prime Scalar.order)
variable (inputSubgroup : Scalar.order • upstream.embed (upstream.promote input) = 0)
variable (inputNonidentity : upstream.embed (upstream.promote input) ≠ 0)
'''
    legal='standardPrime inputSubgroup inputNonidentity'
    source+=f'''include {contracts} {legal} in
theorem inverse_rows_complete (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed {args}) I.rawRows := by
  have done := I.original_inverse_complete {args} {contracts} {legal} {curve}
  intro row member
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (completed {args}) terms = eval (I.completed {args}) terms :=
    H.eval_preserved _ terms (by intro term present; exact P.inverse_rows_outside row member term (inside term present))
  change Square (eval (completed {args}) row.a) (eval (completed {args}) row.b)
  rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
    agrees row.b (by intro term present; exact List.mem_append_right _ present)]
  exact done row member

include {contracts} in
theorem hash_rows_complete : Satisfies (completed {args}) K0.rawRows := by
  have before := constants {args} {contracts}
  exact M.hash_rows_complete _ (before.2.trans before.1.symm)

include {contracts} in
theorem actual_rnk_hash :
    eval (completed {args}) K0.output = Poseidon.hash6
      (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters)
      17 (K0.inputs.map (eval (I.completed {args}))) := by
  have before := constants {args} {contracts}
  exact M.actual_rnk_hash _ before.1 (before.2.trans before.1.symm)

include {contracts} in
theorem actual_rnk_commitment :
    eval (completed {args}) K0.commitment = Poseidon.hash3
      (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters)
      18 [Poseidon.hash6
        (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters)
        17 (K0.inputs.map (eval (I.completed {args})))] := by
  have before := constants {args} {contracts}
  exact M.actual_rnk_commitment _ before.1 (before.2.trans before.1.symm)

include {contracts} {legal} in
theorem original_rows_complete (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed {args}) originalRows := by
  have windows := window_rows_complete {args} {contracts} imaginary nonSquare imaginarySquare
  have inverseRows := inverse_rows_complete {args} {contracts} {legal} {curve}
  have hashes := hash_rows_complete {args} {contracts}
  intro row member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with window | inverseRow
    · exact windows row window
    · exact inverseRows row inverseRow
  · exact hashes row last

include {contracts} in
theorem native_dh_coordinates (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    (⟨completed {args} 3763,completed {args} 3764⟩ : Group.Point F) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote input)) := by
  have xValue := (protected_columns {args} 3763 (by simp [protectedColumns])).trans
    (I.preserves {args} 3763 (by decide))
  have yValue := (protected_columns {args} 3764 (by simp [protectedColumns])).trans
    (I.preserves {args} 3764 (by decide))
  exact (congrArg₂ Group.Point.mk xValue yValue).trans
    (A.native_output_coordinates {args} {contracts} {curve})
'''
    for export in ('protected_columns','window_rows_complete','inverse_rows_complete','hash_rows_complete',
                   'actual_rnk_hash','actual_rnk_commitment','original_rows_complete','native_dh_coordinates'):
        source+='#print axioms '+export+'\n'
    main=_qualify(source+f'end ShielddSecurity.{name}\n',aliases)
    return {fp:footprint,name:main}
