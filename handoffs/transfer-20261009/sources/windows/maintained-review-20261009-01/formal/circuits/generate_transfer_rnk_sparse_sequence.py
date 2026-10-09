"""Bounded actual RNK adapters using one native owned source assignment.

The maintained source emits finite row/write adapters and symbolic sparse
sequencing. It opens no stream. The concrete native application derives source
row truth and independent read agreement, rather than accepting desired target
row truth or desired scalar/output coordinates.
"""
from . import transfer_rnk_completion as sparse, transfer_ownership as owner
from . import generate_transfer_rnk_first_completion as first
from .generate_hash_round import linear, _signature_audits
from .generate_transfer_ivk_reduction_join import _qualify
from .generate_transfer_ownership_constructor_trace import _member, _append


def _row_literal(rows):
    return '[\n'+',\n'.join('  ⟨'+linear(tuple((c,int(v,16)) for c,v in row['a']))+', '+
        linear(tuple((c,int(v,16)) for c,v in row['b']))+'⟩' for row in rows)+'\n]'


def _list_member(index):
    value='List.mem_cons.mpr (Or.inl rfl)'
    for _ in range(index):value='List.mem_cons.mpr (Or.inr ('+value+'))'
    return value


def _validate(plan):
    if not isinstance(plan,dict) or plan.get('schema')!='shieldd-transfer-rnk-all126-sparse-plan-v1' or \
            plan.get('windows')!=126 or len(plan.get('roles',[]))!=134:
        raise owner.relation.RelationError('RNK sequence exact checked all126 plan')
    checked=sparse.sparse_sequence_plan(plan['row_blocks'],domain_size=plan['domain_size'],
        full_rows=plan['full_rows'],protected_columns=plan['protected_columns'])
    if any(checked[key]!=plan[key] for key in checked if key not in ('schema','scope')):
        raise owner.relation.RelationError('RNK sequence unchanged whole structural certificate')
    expected=[]
    for start in range(0,126,16):
        count=min(16,126-start)
        expected.extend(dict(kind='window',window=start+offset,chunk=start) for offset in range(count))
        expected.append(dict(kind='bits',chunk=start,bit_start=2*(126-start-count),width=2*count))
    if plan['roles']!=expected:
        raise owner.relation.RelationError('RNK sequence exact126/252 block roles')
    for column in plan['source_writes']:
        if not (2253<=column<=3008 or 51214<=column<=55994):
            raise owner.relation.RelationError('RNK sequence reviewed whole source write ranges')
    return plan


def generate_blocks(plan):
    """Finite original-row adapters; no native/source truth premise is generated."""
    plan=_validate(plan);result={}
    for index,(role,block,local) in enumerate(zip(plan['roles'],plan['row_blocks'],plan['blocks'])):
        name=f'RuntimeRnkSparseBlock{index:03d}'
        source='import ShielddSecurity.GroupRnkSparseColumns\n'
        original=f'RuntimeOwnershipWindow{role["window"]:03d}' if role['kind']=='window' else None
        if original:source+=f'import ShielddSecurity.{original}\n'
        source+='set_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n'
        source+=f'namespace ShielddSecurity.{name}\n'
        source+=f'def writes : List Nat := {local["source_writes"]}\n'
        source+=f'def support : List Nat := {local["source_support"]}\n'
        source+='def sourceRows : List Row := '+_row_literal(block['source_rows'])+'\n'
        source+='def actualRows : List Row := '+_row_literal(block['target_rows'])+'\n'
        source+='''theorem writes_owned : ∀ column ∈ writes, GroupRnkSparseColumns.Owned column := by
  have checked : writes.all (fun column => decide
    ((2253 ≤ column ∧ column ≤ 3008) ∨ (51214 ≤ column ∧ column ≤ 55994))) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem row_supports : ∀ row ∈ sourceRows, ∀ term ∈ row.a ++ row.b, term.1 ∈ support := by
  have checked : sourceRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∈ support))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
theorem row_coverage : ∀ actual ∈ actualRows, ∃ original ∈ sourceRows,
    Compiler.canonical Scalar.modulus (RowRenaming.linear GroupRnkSparseColumns.columns original.a) =
      Compiler.canonical Scalar.modulus actual.a ∧
    Compiler.canonical Scalar.modulus (RowRenaming.linear GroupRnkSparseColumns.columns original.b) =
      Compiler.canonical Scalar.modulus actual.b := by
  have checked : actualRows.all (fun actual => sourceRows.any (fun original => decide
    (Compiler.canonical Scalar.modulus (RowRenaming.linear GroupRnkSparseColumns.columns original.a) =
       Compiler.canonical Scalar.modulus actual.a ∧
     Compiler.canonical Scalar.modulus (RowRenaming.linear GroupRnkSparseColumns.columns original.b) =
       Compiler.canonical Scalar.modulus actual.b))) = true := by decide
  intro actual member
  obtain ⟨original,present,equal⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked actual member)
  exact ⟨original,present,of_decide_eq_true equal⟩
'''
        if original:
            source+=f'theorem source_rows_owned : sourceRows = {original}.rawRows := by decide\n'
        else:
            source+=f'''theorem source_rows_owned : sourceRows =
    (List.range' {role['bit_start']} {role['width']}).map
      (fun index => booleanRow ({plan['bit_start']}+index)) := by decide
'''
        for export in ('writes_owned','row_supports','row_coverage','source_rows_owned'):
            source+='#print axioms '+export+'\n'
        result[name]=_signature_audits(source+f'end ShielddSecurity.{name}\n')
    return result


def generate_native_source(checked,selection,rnk,transport,reduction_plan,plan):
    """Publish shared native reads once, reusing the first owned input facts."""
    plan=_validate(plan);old,source=first.generate(checked,selection,rnk,transport,reduction_plan)
    name='RuntimeRnkNativeSource'
    source=source.replace('ShielddSecurity.'+old,'ShielddSecurity.'+name)
    ending='end ShielddSecurity.'+name+'\n'
    if not source.endswith(ending):raise owner.relation.RelationError('RNK native source renderer boundary')
    source=source[:-len(ending)]
    source='import ShielddSecurity.RuntimeOwnershipNativeScalar\n'+source
    copy=checked['metadata']['constant_copy'];bits=plan['bit_start']
    def columns_for(accepted,role):
        result=[]
        for value in accepted['points'][role]:
            if value[0]!='source':raise owner.relation.RelationError('RNK exact native unit point role')
            lc=accepted['derived'][value[1]]
            if len(lc)!=1 or lc[0][1]!=1:raise owner.relation.RelationError('RNK exact native unit point LC')
            result.append(lc[0][0])
        if len(result)!=2:raise owner.relation.RelationError('RNK exact native two-coordinate point')
        return result
    sx,sy=columns_for(checked,'base');tx,ty=columns_for(rnk,'base')
    if bits!=2000 or (sx,sy)!=(1504,1505) or columns_for(checked,'output')!=[3007,3008] or \
            columns_for(rnk,'output')!=[3763,3764] or (tx,ty)!=(1520,1521) or \
            plan['nonwritten_support']!=sorted({0,sx,sy,copy,*range(bits,bits+252)}):
        raise owner.relation.RelationError('RNK native source exact reviewed endpoint/independent operand roles')
    source+=f'def sharedColumns : List Nat := {plan["nonwritten_support"]}\n'
    source+=f'def sourceBitRows : List Row := (List.range 252).map (fun index => booleanRow ({bits}+index))\n'
    source+='''include arithmetic initialHash square primitives one linked accepted in
theorem source_original_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (sourceAssignment fq fr model upstream backend codec nk x y input scalar base)
      RuntimeOwnershipConstructorTrace.originalRows :=
  (RuntimeOwnershipNativeConstructor.native_windows_complete fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare).1
include arithmetic initialHash square primitives one linked accepted in
theorem source_boolean_complete :
    Satisfies (sourceAssignment fq fr model upstream backend codec nk x y input scalar base) sourceBitRows := by
  intro row member
  obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
  have bound : index < 252 := List.mem_range.mp present
  have value := RuntimeOwnershipNativeConstructor.native_bit_values fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted index bound
  change Square (eval (sourceAssignment fq fr model upstream backend codec nk x y input scalar base)
    [('''+str(bits)+'''+index,1)]) (eval (sourceAssignment fq fr model upstream backend codec nk x y input scalar base)
    [('''+str(bits)+'''+index,1)])
  simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [value]
  cases RuntimeOwnershipNativeConstructor.nativeBits fr scalar index <;> simp [Square]
include arithmetic initialHash square primitives one linked accepted in
theorem shared_operands (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    ∀ column ∈ sharedColumns,
      sourceAssignment fq fr model upstream backend codec nk x y input scalar base column =
      prefix fq fr model upstream backend codec nk x y input base (columns column) := by
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
      (ShielddPointCoordinateSeed.coordinates fq fr (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
        model upstream backend input '''+str(tx)+' '+str(ty)+''' (by decide) base)
  have bitAgrees (index : Nat) (bound : index < 252) : sigma ('''+str(bits)+'''+index) = target ('''+str(bits)+'''+index) := by
    have sourceValue := RuntimeOwnershipNativeConstructor.native_bit_values fq fr model upstream backend codec nk x y input scalar base
      arithmetic initialHash square primitives one linked accepted index bound
    have targetValue := RuntimeTransferIvkNativeBitValuesOwned.native_values fq fr arithmetic initialHash square primitives backend codec nk x y scalar
      (initial fq fr model upstream backend input base) constants.1 constants.2 accepted index bound
    exact sourceValue.trans targetValue.symm
  intro column member
  have checked : sharedColumns.all (fun column => decide
    (column = 0 ∨ column = '''+str(sx)+' ∨ column = '+str(sy)+' ∨ ('+str(bits)+' ≤ column ∧ column < '+str(bits)+'''+252) ∨ column = '''+str(copy)+''')) = true := by decide
  have shape := of_decide_eq_true (List.all_eq_true.mp checked column member)
  rcases shape with rfl | rfl | rfl | bitBound | rfl
  · have targetValue := RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y
      (initial fq fr model upstream backend input base) 0 (by simp)
    exact sourceFacts.1.trans (targetValue.trans constants.1).symm
  · change sigma '''+str(sx)+' = target '+str(tx)+'''
    exact congrArg Group.Point.x (sourceFacts.2.2.trans targetPoint.symm)
  · change sigma '''+str(sy)+' = target '+str(ty)+'''
    exact congrArg Group.Point.y (sourceFacts.2.2.trans targetPoint.symm)
  · have bound : column-'''+str(bits)+''' < 252 := by omega
    have position : '''+str(bits)+'+(column-'+str(bits)+''') = column := by omega
    have unchanged : columns column = column := by
      have before : ¬ (1504 ≤ column ∧ column ≤ 1505) := by omega
      have low : ¬ (2253 ≤ column ∧ column ≤ 3008) := by omega
      have high : ¬ (51214 ≤ column ∧ column ≤ 55994) := by omega
      simp only [columns,if_neg before,if_neg low,if_neg high]
    rw [unchanged]
    simpa only [position] using bitAgrees (column-'''+str(bits)+''') bound
  · have targetValue := RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y
      (initial fq fr model upstream backend input base) '''+str(copy)+''' (by simp)
    exact sourceFacts.2.1.trans (targetValue.trans (constants.2.trans constants.1)).symm
include arithmetic initialHash square primitives one linked accepted in
theorem native_coordinates (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    (⟨sourceAssignment fq fr model upstream backend codec nk x y input scalar base 3007,
      sourceAssignment fq fr model upstream backend codec nk x y input scalar base 3008⟩ : Group.Point F) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote input)) := by
  have coordinates := RuntimeOwnershipNativeScalar.native_scalar_coordinates fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one four linked accepted imaginary nonSquare imaginarySquare
  simpa only [sourceAssignment,RuntimeOwnershipWindow125.result,eval,Int.cast_one,one_mul,add_zero] using coordinates
'''
    for export in ('source_original_complete','source_boolean_complete','shared_operands','native_coordinates'):
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+ending)


def _native_variables():
    return '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
variable {Extended Subgroup R K Q Signing J Encoded Native : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
variable (upstream : ShielddNativeSdk.Upstream Extended Subgroup R K Q Signing J fq fr
  (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model)
variable (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk x y : Q)
variable (input : Subgroup) (scalar : R) (base : Nat → F)
'''


def _native_contracts(copy):
    return '''variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initialHash : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
variable (one : base 0 = 1) (linked : base '''+str(copy)+''' = base 0)
variable (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
  (ShielddNativeIvkSdkProgram.ivk fq arithmetic initialHash square codec
    (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) nk x y) = some scalar)
'''


def generate_assignment(plan, *, constant_copy):
    """One source assignment and symbolic patches, with independent native reads."""
    plan=_validate(plan)
    name='RuntimeRnkSparseAssignment';blocks=[f'RuntimeRnkSparseBlock{i:03d}' for i in range(134)]
    source='import ShielddSecurity.RuntimeRnkNativeSource\n'
    source+=''.join(f'import ShielddSecurity.{block}\n' for block in blocks)
    source+='set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
    source+=f'namespace ShielddSecurity.{name}\n'
    source+='namespace C := RuntimeRnkNativeSource\nnamespace P := GroupSparseRenamingSequence\n'
    source+='namespace M := GroupRnkSparseColumns\n'
    source+='def writeBlocks : List (List Nat) := ['+', '.join(block+'.writes' for block in blocks)+']\n'
    source+='''theorem block_member (index : Nat) (bound : index < writeBlocks.length) :
    writeBlocks[index] ∈ writeBlocks := List.getElem_mem bound
'''
    source+='''theorem writes_owned : ∀ column ∈ writeBlocks.flatten, M.Owned column := by
  intro column member
  obtain ⟨block,present,inside⟩ := List.mem_flatten.mp member
  simp only [writeBlocks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with '''+' | '.join('rfl' for _ in blocks)+'\n'
    source+=''.join(f'  · exact {block}.writes_owned column inside\n' for block in blocks)
    source+='''theorem write_map_unique : ∀ left ∈ writeBlocks.flatten, ∀ right ∈ writeBlocks.flatten,
    M.columns left = M.columns right → left = right := by
  intro left leftMember right rightMember equal
  exact M.owned_injective left right (writes_owned left leftMember) (writes_owned right rightMember) equal
theorem independent_no_alias : ∀ column ∈ C.sharedColumns,
    M.columns column ∉ writeBlocks.flatten.map M.columns := by
  have checked : C.sharedColumns.all (fun column => decide (column < 2253 ∨ 60775 < column)) = true := by decide
  intro column member mapped
  obtain ⟨written,present,equal⟩ := List.mem_map.mp mapped
  exact M.independent_outside column written
    (of_decide_eq_true (List.all_eq_true.mp checked column member)) (writes_owned written present) equal.symm
'''
    source+=_native_variables()
    source+='''def completed : Nat → F := P.run
  (C.prefix fq fr model upstream backend codec nk x y input base)
  (C.sourceAssignment fq fr model upstream backend codec nk x y input scalar base) M.columns writeBlocks
theorem owned_value (column : Nat) (member : column ∈ writeBlocks.flatten) :
    completed fq fr model upstream backend codec nk x y input scalar base (M.columns column) =
      C.sourceAssignment fq fr model upstream backend codec nk x y input scalar base column :=
  P.run_value _ _ M.columns writeBlocks column member write_map_unique
theorem protected_columns (column : Nat) (outside : column ∉ writeBlocks.flatten.map M.columns) :
    completed fq fr model upstream backend codec nk x y input scalar base column =
      C.prefix fq fr model upstream backend codec nk x y input base column :=
  P.run_outside _ _ M.columns writeBlocks column outside
'''
    # Supply the actual accepted observer role; support extrema are not an
    # authority for inventing a constant-copy handle or column.
    copy=owner.relation.natural(constant_copy,plan['domain_size'])
    if copy<=60775 or copy not in plan['nonwritten_support']:
        raise owner.relation.RelationError('RNK sequence exact accepted independent copy role')
    source+=_native_contracts(copy)
    source+='''include arithmetic initialHash square primitives one linked accepted in
theorem shared_value (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    ∀ column ∈ C.sharedColumns,
      completed fq fr model upstream backend codec nk x y input scalar base (M.columns column) =
      C.sourceAssignment fq fr model upstream backend codec nk x y input scalar base column := by
  intro column member
  have kept := protected_columns fq fr model upstream backend codec nk x y input scalar base
    (M.columns column) (independent_no_alias column member)
  have read := C.shared_operands fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare column member
  exact kept.trans read.symm
include arithmetic initialHash square primitives one linked accepted in
theorem native_output_coordinates (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    (⟨completed fq fr model upstream backend codec nk x y input scalar base 3763,
      completed fq fr model upstream backend codec nk x y input scalar base 3764⟩ : Group.Point F) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote input)) := by
'''
    ownership={column:index for index,block in enumerate(plan['blocks']) for column in block['source_writes']}
    for column in (3007,3008):
        if column not in ownership:raise owner.relation.RelationError('RNK actual final output requires owned mapped write')
        index=ownership[column]
        source+=f'''  have member{column} : {column} ∈ writeBlocks.flatten := by
    apply List.mem_flatten.mpr
    exact ⟨{blocks[index]}.writes,block_member {index} (by decide),by decide⟩
'''
    source+='''  have point := congrArg₂ Group.Point.mk
    (owned_value fq fr model upstream backend codec nk x y input scalar base 3007 member3007)
    (owned_value fq fr model upstream backend codec nk x y input scalar base 3008 member3008)
  exact point.trans (C.native_coordinates fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted four imaginary nonSquare imaginarySquare)
'''
    for export in ('block_member','writes_owned','write_map_unique','independent_no_alias','owned_value','protected_columns',
                   'shared_value','native_output_coordinates'):
        source+='#print axioms '+export+'\n'
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',
        dict(C='RuntimeRnkNativeSource',P='GroupSparseRenamingSequence',M='GroupRnkSparseColumns'))


def generate_native_chunks(plan, *, constant_copy):
    """Eight opaque compositions; each physical row adapter stays <=512 rows.

    The only source assignment is RuntimeRnkNativeSource.sourceAssignment,
    literally the maintained native126 constructor. No satisfaction, desired
    point, desired scalar, or nonidentity conclusion is a caller premise.
    """
    plan=_validate(plan);copy=owner.relation.natural(constant_copy,plan['domain_size'])
    if copy not in plan['nonwritten_support']:raise owner.relation.RelationError('RNK native chunks accepted copy role')
    write_owner={column:index for index,block in enumerate(plan['blocks']) for column in block['source_writes']}
    result={}
    for chunk_index,start in enumerate(range(0,126,16)):
        indices=[index for index,role in enumerate(plan['roles']) if role['chunk']==start]
        name=f'RuntimeRnkNativeChunk{start:03d}'
        source='import ShielddSecurity.RuntimeRnkSparseAssignment\n'
        source+='set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
        source+=f'namespace ShielddSecurity.{name}\n'
        aliases=dict(C='RuntimeRnkNativeSource',A='RuntimeRnkSparseAssignment',
            M='GroupRnkSparseColumns',P='GroupSparseRenamingCompletion',G='RuntimeOwnershipConstructorTrace')
        source+=''.join(f'namespace {key} := {value}\n' for key,value in aliases.items())
        source+='def rowBlocks : List (List Row) := ['+', '.join(f'RuntimeRnkSparseBlock{i:03d}.actualRows' for i in indices)+']\n'
        source+='def actualRows : List Row := rowBlocks.flatten\n'
        source+=_native_variables()+_native_contracts(copy)
        for index in indices:
            block=f'RuntimeRnkSparseBlock{index:03d}';role=plan['roles'][index]
            source+='''include arithmetic initialHash square primitives one linked accepted in
private theorem block'''+str(index)+'''_agrees (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    ∀ column ∈ '''+block+'''.support,
      A.completed fq fr model upstream backend codec nk x y input scalar base (M.columns column) =
      C.sourceAssignment fq fr model upstream backend codec nk x y input scalar base column := by
  intro column member
  simp only ['''+block+'''.support,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in plan['blocks'][index]['source_support'])+'\n'
            for column in plan['blocks'][index]['source_support']:
                if column in write_owner:
                    owning=write_owner[column]
                    source+=f'''  · apply A.owned_value fq fr model upstream backend codec nk x y input scalar base {column}
    exact List.mem_flatten.mpr ⟨RuntimeRnkSparseBlock{owning:03d}.writes,
      A.block_member {owning} (by decide),by decide⟩
'''
                elif column in plan['nonwritten_support']:
                    source+=f'''  · exact A.shared_value fq fr model upstream backend codec nk x y input scalar base
      arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare {column} (by decide)
'''
                else:raise owner.relation.RelationError('RNK native row support outside whole read/write certificate')
            source+='''include arithmetic initialHash square primitives one linked accepted in
private theorem block'''+str(index)+'''_source (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (C.sourceAssignment fq fr model upstream backend codec nk x y input scalar base)
      '''+block+'''.sourceRows := by
  intro row member
  rw ['''+block+'''.source_rows_owned] at member
'''
            if role['kind']=='window':
                window=role['window'];stem=f'RuntimeOwnershipWindow{window:03d}'
                stems=[f'RuntimeOwnershipWindow{value:03d}.rawRows' for value in range(start,min(start+16,126))]
                chunk=f'RuntimeOwnershipConstructorChunk{start:03d}'
                source+=f'''  have within : row ∈ {chunk}.originalRows := by
    change row ∈ {chunk}.originalBlocks.flatten
    apply List.mem_flatten.mpr
    refine ⟨{stem}.rawRows,?_,member⟩
    change {stem}.rawRows ∈ [{', '.join(stems)}]
    exact {_list_member(window-start)}
  apply C.source_original_complete fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare row
  change row ∈ '''+_append(f'RuntimeOwnershipConstructorChunk{value:03d}.originalRows' for value in range(0,126,16))+'\n'
                source+='  exact '+_member(chunk_index,8,'within')+'\n'
            else:
                source+='''  obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
  have bound : index < 252 := by
    obtain ⟨offset,offsetBound,position⟩ := List.mem_range'.mp present
    simp only [Nat.one_mul] at position
    omega
  apply C.source_boolean_complete fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted
  change booleanRow ('''+str(plan['bit_start'])+'''+index) ∈
    (List.range 252).map (fun index => booleanRow ('''+str(plan['bit_start'])+'''+index))
  exact List.mem_map.mpr ⟨index,List.mem_range.mpr bound,rfl⟩
'''
            source+='''include arithmetic initialHash square primitives one linked accepted in
private theorem block'''+str(index)+'''_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (A.completed fq fr model upstream backend codec nk x y input scalar base)
      '''+block+'''.actualRows := by
  let built := A.completed fq fr model upstream backend codec nk x y input scalar base
  let sigma := C.sourceAssignment fq fr model upstream backend codec nk x y input scalar base
  have agrees := block'''+str(index)+'''_agrees fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare
  have sourceRows := block'''+str(index)+'''_source fq fr model upstream backend codec nk x y input scalar base
    arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare
  -- Agreement was derived using the whole patch sequence and its whole-write
  -- injection/exclusion certificates. This call transports rows without any
  -- additional writes, so the constructed target assignment is retained.
  have transported := P.rows_complete built sigma M.columns [] '''+block+'.support '+block+'.sourceRows '+block+'''.actualRows
    (by intro left member; exact False.elim (List.not_mem_nil member))
    (by intro column member outside; simp only [List.map_nil,List.not_mem_nil,not_false_eq_true])
    (by intro column member outside; exact (agrees column member).symm)
    '''+block+'.row_supports '+block+'''.row_coverage sourceRows
  simpa only [P.extend,patchAssignment,List.map_nil,List.not_mem_nil,if_false] using transported
'''
        source+='''include arithmetic initialHash square primitives one linked accepted in
theorem actual_rows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (A.completed fq fr model upstream backend codec nk x y input scalar base) actualRows := by
  intro row member
  obtain ⟨block,present,inside⟩ := List.mem_flatten.mp member
  simp only [rowBlocks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with '''+' | '.join('rfl' for _ in indices)+'\n'
        for index in indices:
            source+=f'''  · exact block{index}_complete fq fr model upstream backend codec nk x y input scalar base
      arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare row inside
'''
        source+='#print axioms actual_rows_complete\n'
        result[name]=_qualify(source+f'end ShielddSecurity.{name}\n',aliases)
    return result


def generate_join(plan, *, constant_copy):
    """All126 actual RNK rows and the same Fr native DH on one assignment."""
    plan=_validate(plan);copy=owner.relation.natural(constant_copy,plan['domain_size'])
    names=[f'RuntimeRnkNativeChunk{start:03d}' for start in range(0,126,16)]
    name='RuntimeRnkNativeCompletion'
    source=''.join(f'import ShielddSecurity.{chunk}\n' for chunk in names)
    source+='set_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n'
    source+=f'namespace ShielddSecurity.{name}\nnamespace A := RuntimeRnkSparseAssignment\n'
    source+='def actualRows : List Row := '+_append(chunk+'.actualRows' for chunk in names)+'\n'
    source+=_native_variables()+_native_contracts(copy)
    source+='''include arithmetic initialHash square primitives one linked accepted in
theorem actual_rows_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (A.completed fq fr model upstream backend codec nk x y input scalar base) actualRows := by
  intro row member
  simp only [actualRows,List.mem_append] at member
  rcases member with '''+' | '.join('present' for _ in names)+'\n'
    for chunk in names:
        source+=f'''  · exact {chunk}.actual_rows_complete fq fr model upstream backend codec nk x y input scalar base
      arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare row present
'''
    source+='''include arithmetic initialHash square primitives one linked accepted in
theorem actual_native_dh (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (A.completed fq fr model upstream backend codec nk x y input scalar base) actualRows ∧
      (⟨A.completed fq fr model upstream backend codec nk x y input scalar base 3763,
        A.completed fq fr model upstream backend codec nk x y input scalar base 3764⟩ : Group.Point F) =
      model.coordinates (fr.integer scalar • upstream.embed (upstream.promote input)) :=
  ⟨actual_rows_complete fq fr model upstream backend codec nk x y input scalar base
     arithmetic initialHash square primitives one linked accepted imaginary nonSquare imaginarySquare,
   A.native_output_coordinates fq fr model upstream backend codec nk x y input scalar base
     arithmetic initialHash square primitives one linked accepted four imaginary nonSquare imaginarySquare⟩
#print axioms actual_rows_complete
#print axioms actual_native_dh
'''
    return name,_qualify(source+f'end ShielddSecurity.{name}\n',dict(A='RuntimeRnkSparseAssignment'))
