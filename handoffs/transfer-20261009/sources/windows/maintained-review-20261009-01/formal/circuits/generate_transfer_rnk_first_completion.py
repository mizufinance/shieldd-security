"""Actual first RNK window from native input and the same owned SDK Fr.

The full source constructor is reused as a proved functional assignment, not
assumed row truth. Only actual first-window writes are copied to the RNK loop.
NativeLegalSrc/caller input association and later126/inverse/hash joins remain
separate. This renderer never scans the ordinary relation.
"""
from . import transfer_ownership as owner, transfer_ownership_completion as owned
from . import transfer_rnk_completion as sparse
from .generate_hash_round import linear
from .generate_transfer_ivk_reduction_join import _qualify
from .generate_transfer_ownership_constructor_trace import _append


def generate(checked, selected, rnk, transport, reduction_plan):
    metadata=checked['metadata'];other=rnk['metadata'];identity=transport['identity']
    if metadata['schema']!='shieldd-transfer-ownership-v1' or other['schema']!='shieldd-transfer-rnk-dh-v1' or \
            any(value['window_start']!=0 or value['window_count']!=16 for value in (metadata,other)):
        raise owner.relation.RelationError('RNK first completion exact accepted first chunks')
    for key,identity_key in (('relation_digest','relation_digest'),('domain_size','domain_size'),('full_rows','stored_rows')):
        if metadata[key]!=other[key] or metadata[key]!=identity[identity_key]:
            raise owner.relation.RelationError('RNK first completion same actual relation shape')
    if checked['bits']!=rnk['bits'] or metadata['constant_copy']!=other['constant_copy']:
        raise owner.relation.RelationError('RNK first completion shared scalar/copy roles')
    bits=[checked['derived'][handle] for handle in checked['bits']]
    if len(bits)!=252 or any(len(lc)!=1 or lc[0][1]!=1 for lc in bits):
        raise owner.relation.RelationError('RNK first completion exact scalar singletons')
    bit_start=bits[0][0][0]
    if bits!=[((bit_start+i,1),) for i in range(252)]:
        raise owner.relation.RelationError('RNK first completion contiguous accepted scalar bits')
    q,r=reduction_plan['phases'][:2]
    if q['width']!=4 or r['width']!=252 or r['start']!=bit_start or \
            reduction_plan['checked']['metadata']['relation_digest']!=metadata['relation_digest']:
        raise owner.relation.RelationError('RNK first completion accepted reduction bit/source join')
    def columns_for(accepted,role):
        values=[accepted['derived'][value[1]] for value in accepted['points'][role] if value[0]=='source']
        if len(values)!=2 or any(len(lc)!=1 or lc[0][1]!=1 for lc in values):
            raise owner.relation.RelationError('RNK first completion native input unit roles')
        return [lc[0][0] for lc in values]
    sx,sy=columns_for(checked,'base');tx,ty=columns_for(rnk,'base')
    if [owner.rnk_column_candidate(column) for column in (sx,sy)]!=[tx,ty]:
        raise owner.relation.RelationError('RNK first completion observed input source map')
    block=transport['chunks'][0]
    if block['start']!=0 or block['count']!=16 or len(block['blocks'])!=17:
        raise owner.relation.RelationError('RNK first completion retained canonical first block')
    local=owned.window_plan(checked,selected,0,True)
    raw={row['row']:row for row in selected['selected_rows']}
    source_rows=[raw[index] for index in local['local_rows']]
    target_rows=block['blocks'][0];copy=metadata['constant_copy']
    protected=sorted({0,1512,1513,tx,ty,1980,1981,1993,3007,3008,3766,copy})
    plan=sparse.sparse_transport_plan(source_rows,target_rows,local['writes'],
        domain_size=metadata['domain_size'],full_rows=metadata['full_rows'],protected_columns=protected)
    if plan['nonwritten_support']!=sorted([0,sx,sy,bit_start+250,bit_start+251,copy]):
        raise owner.relation.RelationError('RNK first completion exact independent nonwritten operands')
    name='RuntimeRnkWindow000Completion'
    aliases=dict(N='RuntimeOwnershipNativeConstructor',G='RuntimeOwnershipConstructorTrace',
        C0='RuntimeOwnershipConstructorChunk000',W='RuntimeOwnershipWindow000',
        T='RuntimeOwnershipWindow000NativeTables',F0='RuntimeOwnershipWindow000PrecomputeFrame',
        IV='RuntimeTransferIvkNativeInverseOwned',V='RuntimeTransferIvkNativeBitValuesOwned',
        H='RuntimeTransferIvkHashOwnedCompletion',I='RuntimeTransferIvkInverseOwnedCompletion',
        O='RuntimeTransferIvkReductionProductOrder',S0='ShielddViewingKeySeed',
        D='RuntimeHashBlock_authorization_ivk_0',P='GroupSparseRenamingCompletion',
        R0='RuntimeRnkTrace000',SC='ShielddPointCoordinateSeed')
    source=''.join('import ShielddSecurity.'+aliases[key]+'\n' for key in ('N','F0','R0','P'))
    source+='import ShielddSecurity.ScalarReductionFrame\n'
    source+='set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
    source+=f'namespace ShielddSecurity.{name}\n'
    source+=''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
    source+='''def columns (column : Nat) : Nat :=
  if 1504 ≤ column ∧ column ≤ 1505 then column + 16
  else if 2253 ≤ column ∧ column ≤ 3008 then column + 756
  else if 51214 ≤ column ∧ column ≤ 55994 then column + 4781
  else column
'''
    source+=f'def writes : List Nat := {plan["source_writes"]}\ndef support : List Nat := {plan["source_support"]}\n'
    source+=f'def protectedColumns : List Nat := {protected}\n'
    for label,rows in (('sourceRows',source_rows),('actualRows',target_rows)):
        source+=f'def {label} : List Row := [\n'+',\n'.join('  ⟨'+linear(tuple((c,int(v,16)) for c,v in row['a']))+','+
            linear(tuple((c,int(v,16)) for c,v in row['b']))+'⟩' for row in rows)+']\n'
    source+='''theorem source_rows_owned : sourceRows = W.rawRows := by decide
theorem columns_support : ∀ column ∈ support, columns column = R0.columns column := by
  have checked : support.all (fun column => decide (columns column = R0.columns column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem write_map_unique : ∀ left ∈ writes, ∀ right ∈ writes,
    columns left = columns right → left = right := by
  have checked : writes.all (fun left => writes.all (fun right =>
    decide (columns left = columns right → left = right))) = true := by decide
  intro left leftMember right rightMember
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked left leftMember) right rightMember)
theorem support_no_alias : ∀ column ∈ support, column ∉ writes → columns column ∉ writes.map columns := by
  have checked : support.all (fun column => decide
    (column ∈ writes ∨ columns column ∉ writes.map columns)) = true := by decide
  intro column member outside
  exact (of_decide_eq_true (List.all_eq_true.mp checked column member)).resolve_left outside
'''
    source+='''private theorem row_supports : ∀ row ∈ sourceRows, ∀ term ∈ row.a ++ row.b, term.1 ∈ support := by
  have checked : sourceRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∈ support))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
private theorem row_coverage : ∀ actual ∈ actualRows, ∃ original ∈ sourceRows,
    Compiler.canonical Scalar.modulus (RowRenaming.linear columns original.a) = Compiler.canonical Scalar.modulus actual.a ∧
    Compiler.canonical Scalar.modulus (RowRenaming.linear columns original.b) = Compiler.canonical Scalar.modulus actual.b := by
  have checked : actualRows.all (fun actual => sourceRows.any (fun original => decide
    (Compiler.canonical Scalar.modulus (RowRenaming.linear columns original.a) = Compiler.canonical Scalar.modulus actual.a ∧
     Compiler.canonical Scalar.modulus (RowRenaming.linear columns original.b) = Compiler.canonical Scalar.modulus actual.b))) = true := by decide
  intro actual member
  obtain ⟨original,present,equal⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked actual member)
  exact ⟨original,present,of_decide_eq_true equal⟩
private theorem source_included : ∀ row ∈ sourceRows, row ∈ G.originalRows := by
  intro row member
  rw [source_rows_owned] at member
  change row ∈ C0.originalRows ++ ('''+_append(f'RuntimeOwnershipConstructorChunk{start:03d}.originalRows' for start in range(16,126,16))+''')
  apply List.mem_append_left
  change row ∈ C0.originalBlocks.flatten
  apply List.mem_flatten.mpr
  refine ⟨W.rawRows,?_,member⟩
  simp only [C0.originalBlocks,List.mem_cons,List.not_mem_nil,or_false]
  exact Or.inl rfl
'''
    source+='''variable {F : Type} [Field F] [CharP F Scalar.modulus]
variable {Extended Subgroup R K Q Signing J Encoded Native : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream Extended Subgroup R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q) (input : Subgroup) (scalar : R) (base : Nat → F)
'''
    source+=f'''def initial : Nat → F := SC.seed fq fr (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
  model upstream backend input {tx} {ty} base
def prefix : Nat → F := IV.completeAssignment fq backend codec nk x y
  (initial fq fr model upstream backend input base)
def sourceAssignment : Nat → F := N.completed fq fr model upstream backend codec nk x y input scalar base
def completed : Nat → F := P.extend (prefix fq fr model upstream backend codec nk x y input base)
  (sourceAssignment fq fr model upstream backend codec nk x y input scalar base) columns writes
'''
    source+='''variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initialHash : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
'''
    source+=f'''variable (one : base 0 = 1) (linked : base {copy} = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initialHash square codec
    (Poseidon.castParameters D.parameters) nk x y) = some scalar)
include one linked in
private theorem initial_constants : initial fq fr model upstream backend input base 0 = 1 ∧
    initial fq fr model upstream backend input base {copy} = initial fq fr model upstream backend input base 0 := by
  have kept (column : Nat) (outside : column ∉ SC.columns {tx} {ty}) :=
    SC.seed_preserves fq fr (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
      model upstream backend input {tx} {ty} base column outside
  exact ⟨(kept 0 (by decide)).trans one,by rw [kept {copy} (by decide),kept 0 (by decide),linked]⟩
private theorem ivk_input_preserved (column : Nat) (member : column ∈ [{tx},{ty}]) :
    prefix fq fr model upstream backend codec nk x y input base column =
      initial fq fr model upstream backend input base column := by
  have checks : [{tx},{ty}].all (fun column => decide
      (column ∉ [{q['value'][0][0]},{r['value'][0][0]}] ∧
       (column < {q['start']} ∨ {q['start']}+4 ≤ column) ∧
       (column < {r['start']} ∨ {r['start']}+252 ≤ column) ∧
       column ∉ PoseidonCompletion.writes O.allStages ∧
       column ∉ I.ownedWrites ∧ column ∉ H.ownedWrites ∧ column ∉ S0.columns)) = true := by decide
  have facts := of_decide_eq_true (List.all_eq_true.mp checks column member)
  let seeded := S0.seed fq backend nk x y (initial fq fr model upstream backend input base)
  let hashed := H.completeAssignment seeded
  let value := eval hashed O.hashValue
  exact (I.preserves _ column facts.2.2.2.2.1).trans
    ((ScalarReductionFrame.column hashed codec value {q['value'][0][0]} {r['value'][0][0]} {q['start']} {r['start']}
      O.allStages column facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1).trans
      ((H.preserves seeded column facts.2.2.2.2.2.1).trans
        (S0.seed_preserves fq backend nk x y _ column facts.2.2.2.2.2.2)))
'''
    # The remainder is kept as small typed facts rather than unfolding either
    # entire completed assignment inside the finite sparse transport proof.
    source+='''include arithmetic initialHash square primitives one linked accepted in
private theorem source_facts (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    sourceAssignment fq fr model upstream backend codec nk x y input scalar base 0 = 1 ∧
'''+f'''    sourceAssignment fq fr model upstream backend codec nk x y input scalar base {copy} = 1 ∧
    (⟨sourceAssignment fq fr model upstream backend codec nk x y input scalar base {sx},
      sourceAssignment fq fr model upstream backend codec nk x y input scalar base {sy}⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.promote input)) := by
  let ivk := IV.completeAssignment fq backend codec nk x y base
  let precomputed := N.precomputed fq fr model upstream backend codec nk x y input base
  let built := sourceAssignment fq fr model upstream backend codec nk x y input scalar base
  have ivkOne : ivk 0 = 1 := (N.ivk_constants fq backend codec nk x y base 0 (by simp)).trans one
  have ivkLink : ivk {copy} = ivk 0 := by
    rw [N.ivk_constants fq backend codec nk x y base {copy} (by simp),
      N.ivk_constants fq backend codec nk x y base 0 (by simp),linked]
  have windows := N.native_windows_complete fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare
  have kept (column : Nat) (bound : column < 2257) : built column = precomputed column :=
    windows.2.2.2 column (List.mem_append_left _ (List.mem_range.mpr bound))
  have oneBuilt : built 0 = 1 := (kept 0 (by decide)).trans
    ((T.protected_columns fq fr model upstream backend input ivk ivkLink 0 (by decide)).trans ivkOne)
  have copyKept : built {copy} = precomputed {copy} :=
    windows.2.2.2 {copy} (List.mem_append_right _ (by simp))
  have copyBuilt : built {copy} = 1 := copyKept.trans
    ((T.protected_columns fq fr model upstream backend input ivk ivkLink {copy} (by decide)).trans
      (ivkLink.trans ivkOne))
  have pointBuilt : (⟨built {sx},built {sy}⟩ : Group.Point F) =
      (⟨precomputed {sx},precomputed {sy}⟩ : Group.Point F) :=
    congrArg₂ Group.Point.mk (kept {sx} (by decide)) (kept {sy} (by decide))
  have read := (T.table_coordinates fq fr model upstream backend input ivk imaginary nonSquare imaginarySquare ivkOne ivkLink).1
  have readValue : (⟨precomputed {sx},precomputed {sy}⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.promote input)) := by
    simpa only [T.tables,RuntimeOwnershipWindow000Program.tables,GroupFixedCircuitCompletion.point,
      eval,Int.cast_one,one_mul,add_zero] using read
  exact ⟨oneBuilt,copyBuilt,pointBuilt.trans readValue⟩
'''
    source+='''include arithmetic initialHash square primitives one linked accepted in
theorem actual_rows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed fq fr model upstream backend codec nk x y input scalar base) actualRows := by
  let sigma := sourceAssignment fq fr model upstream backend codec nk x y input scalar base
  let target := prefix fq fr model upstream backend codec nk x y input base
  have constants := initial_constants fq fr model upstream backend input base one linked
  have sourceFacts := source_facts fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare
  have targetPoint : (⟨target '''+str(tx)+',target '+str(ty)+'''⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.promote input)) := by
    exact (congrArg₂ Group.Point.mk
      (ivk_input_preserved fq fr model upstream backend codec nk x y input base '''+str(tx)+''' (by simp))
      (ivk_input_preserved fq fr model upstream backend codec nk x y input base '''+str(ty)+''' (by simp))).trans
      (SC.coordinates fq fr (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
        model upstream backend input '''+str(tx)+' '+str(ty)+''' (by decide) base)
  have bitAgrees (index : Nat) (bound : index < 252) : sigma ('''+str(bit_start)+'''+index) = target ('''+str(bit_start)+'''+index) := by
    have sourceValue := N.native_bit_values fq fr model upstream backend codec nk x y input scalar base
      arithmetic initialHash square primitives one linked accepted index bound
    have targetValue := V.native_values fq fr arithmetic initialHash square primitives backend codec nk x y scalar
      (initial fq fr model upstream backend input base) constants.1 constants.2 accepted index bound
    exact sourceValue.trans targetValue.symm
  have sourceTrue : Satisfies sigma sourceRows := by
    have rows := (N.native_windows_complete fq fr model upstream backend codec nk x y input scalar base
      arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare).1
    intro row member
    exact rows row (source_included row member)
  apply P.rows_complete target sigma columns writes support sourceRows actualRows
    write_map_unique support_no_alias ?_ row_supports row_coverage sourceTrue
  intro column member outside
  have remaining : column ∈ '''+str(plan['nonwritten_support'])+''' := by
    have checked : support.all (fun column => decide (column ∈ writes ∨ column ∈ '''+str(plan['nonwritten_support'])+''')) = true := by decide
    exact (of_decide_eq_true (List.all_eq_true.mp checked column member)).resolve_left outside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at remaining
  rcases remaining with '''+' | '.join('rfl' for _ in plan['nonwritten_support'])+'\n'
    for column in plan['nonwritten_support']:
        if column in (0,copy):
            fact='sourceFacts.1' if column==0 else 'sourceFacts.2.1'
            source+=f'''  · have targetValue := N.ivk_constants fq backend codec nk x y
      (initial fq fr model upstream backend input base) {column} (by simp)
    have initialValue : initial fq fr model upstream backend input base {column} = 1 := '''+(
        'constants.1' if column==0 else 'constants.2.trans constants.1')+f'''
    exact {fact}.trans (targetValue.trans initialValue).symm
'''
        elif column in (sx,sy):
            axis='x' if column==sx else 'y'
            source+=f'''  · have paired := sourceFacts.2.2.trans targetPoint.symm
    exact congrArg Group.Point.{axis} paired
'''
        else:
            source+=f'  · exact bitAgrees {column-bit_start} (by decide)\n'
    source+='''theorem protected_columns : ∀ column ∈ protectedColumns,
    completed fq fr model upstream backend codec nk x y input scalar base column =
      prefix fq fr model upstream backend codec nk x y input base column := by
  have checked : protectedColumns.all (fun column => decide (column ∉ writes.map columns)) = true := by decide
  intro column member
  exact P.extend_preserves _ _ columns writes column
    (of_decide_eq_true (List.all_eq_true.mp checked column member))
'''
    exports=('source_rows_owned','columns_support','write_map_unique','support_no_alias','actual_rows_complete','protected_columns')
    for export in exports:source+='#print axioms '+export+'\n'
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',aliases)
