"""Optional constructive transport after strict genuine48/one-replay acceptance.

Only the source-scope constructor is reused. Every target keeps its exact
original rows, operands, native scalar/publication roles and outside-write
frame. Unsupported correspondence uses the unchanged per-scope generators.
No runtime qualification or Lean acceptance is asserted by this renderer.
"""
from . import transfer_epk_fixed_renaming as matcher
from . import transfer_epk_fixed_sequence as sequence,transfer_epk_fixed_program as program
from . import transfer_epk_fixed_completion as local,transfer_relation as relation
from .transfer_balance_rows import canonical,source_index
from .generate_hash_round import linear,_signature_audits

CERTIFICATE_COLUMNS=128
CERTIFICATE_ROWS=1024


def _balanced(items):
    if not items:return 'FiniteColumnRenaming.Tree.empty'
    if len(items)==1:return items[0][1]
    middle=len(items)//2
    return f'(.branch {items[middle][0]} {_balanced(items[:middle])} {_balanced(items[middle:])})'


def _map_source(pair):
    ns=f'RuntimeTransferEpk{pair["scope_id"]}RenamingMap'
    pairs=pair['permutation']
    if len(pairs)>2*matcher.MAX_COLUMNS or len({p[0] for p in pairs})!=len(pairs):
        raise relation.RelationError('EPK proof finite map support/unique keys')
    if pairs!=sorted(pairs):raise relation.RelationError('EPK proof map sorted exact keys')
    mapping=dict(pairs)
    if any(mapping.get(target,target)!=source for source,target in pairs):
        raise relation.RelationError('EPK proof finite map inverse refused')
    out=['import ShielddSecurity.FiniteColumnRenaming\n',f'namespace ShielddSecurity.{ns}\n',
         'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n']
    parts=[]
    for ordinal,start in enumerate(range(0,len(pairs),CERTIFICATE_COLUMNS)):
        page=pairs[start:start+CERTIFICATE_COLUMNS];name=f'part{ordinal}'
        out.append(f'def {name} : FiniteColumnRenaming.Tree := '+_balanced([
            (source,f'(.leaf {source} {target})') for source,target in page])+'\n')
        parts.append((page[0][0],name))
    out.append('def tree : FiniteColumnRenaming.Tree := '+_balanced(parts)+'\n')
    out.append('def columns : Nat → Nat := FiniteColumnRenaming.column tree\n')
    names=[]
    for ordinal,(_,part) in enumerate(parts):
        name=f'inverse_part{ordinal}';names.append(name)
        out.append(f'theorem {name} : FiniteColumnRenaming.checkInverse tree {part} = true := by decide\n')
    # The Boolean assembly has the same balanced structure, without traversing
    # any leaf or row support again in the final checked-order-style proof.
    def conjunction(items):
        if not items:return 'true'
        if len(items)==1:return f'(FiniteColumnRenaming.checkInverse tree {items[0][1]})'
        middle=len(items)//2
        return f'({conjunction(items[:middle])} && {conjunction(items[middle:])})'
    out.append('theorem inverse_checked : FiniteColumnRenaming.checkInverse tree tree = true := by\n'
        +'  change '+conjunction(parts)+' = true\n'
        +('  rw ['+','.join(names)+']\n' if names else '')+'  rfl\n')
    out.append('theorem inverted (column : Nat) : columns (columns column) = column :=\n'
               '  FiniteColumnRenaming.involutive tree inverse_checked column\n'
               'theorem injective : Function.Injective columns :=\n'
               '  FiniteColumnRenaming.injective tree inverse_checked\n')
    out.append('def protectedOriginals : List Nat := [0,1,2,6,200692]\n'
               'theorem protected_checked : protectedOriginals.all (fun column => decide (columns column = column)) = true := by decide\n'
               'theorem protected_fixed : ∀ column ∈ protectedOriginals, columns column = column := by\n'
               '  intro column member\n'
               '  exact of_decide_eq_true (List.all_eq_true.mp protected_checked column member)\n')
    out.extend('#print axioms '+name+'\n' for name in names+[
        'inverse_checked','inverted','injective','protected_checked','protected_fixed'])
    out.append(f'end ShielddSecurity.{ns}\n')
    return ns,_signature_audits(''.join(out))


def _window_indices(checked,selection,offset):
    """Exact authored Window.rawRows ordering, including retained copy repeats.

    This uses the same already checked product/quotient certificates; it does
    not guess physical rows from a source handle or a row hash.
    """
    raw,normalized,products,quotients=local.selection(checked,selection)
    obj=checked['metadata'];index=obj['window_start']+offset;copy=obj['constant_copy']
    roles=[f'window.{index}.select.0',f'window.{index}.select.1',
           *[f'window.{index}.{name}' for name in ('xx','yy','sum','xy')]]
    used={i for role in roles for i in products[role]['rows']}
    links=[i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if len(links)!=1:raise relation.RelationError('EPK proof exact window copy row')
    used.add(links[0]);qused={links[0]}
    for handle in obj['bits'][2*index:2*index+2]:
        bit=checked['observed'][source_index(handle)]
        matches=[i for i,row in normalized.items() if row==(bit,bit)]
        if len(matches)!=1:raise relation.RelationError('EPK proof unique window Boolean row')
        used.add(matches[0])
    for axis in range(2):qused.update(quotients[f'window.{index}.quotient.{axis}']['rows'])
    return sorted(used)+sorted(qused)


def _blocks(source):
    blocks=[]
    for chunk,selection in zip(source['chunks'],source['selections']):
        start=chunk['metadata']['window_start']
        for offset in range(chunk['metadata']['window_count']):
            index=start+offset
            blocks.append(dict(module=f'RuntimeTransferEpk0FixedWindow{index:03d}',
                definition='rawRows',indices=_window_indices(chunk,selection,offset)))
    blocks.append(dict(module='RuntimeTransferEpk0Canonical',definition='originalRows',
        indices=_canonical_indices(source)))
    boundary=source['boundary'];copy=source['checked']['parent']['constant_copy']
    links=[i for i,row in source['boundary_raw'].items()
        if row==(canonical([(0,1),(copy,-1)]),())]
    if len(links)!=1:raise relation.RelationError('EPK proof exact native copy row')
    blocks.append(dict(module='RuntimeTransferEpk0NativeBoundary',definition='inverseRows',
        indices=boundary['inverse_certificate']['rows']))
    blocks.append(dict(module='RuntimeTransferEpk0NativeBoundary',definition='bindingRows',
        indices=sorted({i for b in boundary['bindings'] for i in b['rows']}|set(links))))
    return blocks


def _canonical_indices(source):
    """Exact checked canonical renderer order, not physical sorting.

    Its 16-bit blocks contain Boolean rows first, then each bit's product
    pair. The final block retains copy, reconstruction and endpoint order.
    """
    from . import transfer_recovery_canonical as comparator
    raw=source['canonical_raw'];scalar=source['scalar'];copy=source['checked']['parent']['constant_copy']
    normalized={index:tuple(canonical((0 if column==copy else column,value) for column,value in lc)
        for lc in row) for index,row in raw.items()}
    columns=list(range(scalar['bit_start'],scalar['bit_start']+252))
    selected=dict(checked=source['chunks'][0],columns=columns,value=scalar['value'],
        weighted=canonical((column,pow(2,index,relation.MODULUS)) for index,column in enumerate(columns)))
    certificate,used=comparator._chain(selected,raw,normalized)
    if used!=set(raw):raise relation.RelationError('EPK canonical authored basis exact original coverage')
    roles={role:item['row'] for item in certificate['templates'] for role in item['roles']}
    products={item['step']:item['rows'] for item in certificate['products']}
    ordered=[]
    for start in range(0,252,16):
        bits=list(range(start,min(start+16,252)))
        ordered.extend(roles['boolean'+str(bit)] for bit in bits)
        ordered.extend(index for bit in bits for index in products.get(bit,[]))
    ordered.extend(roles[role] for role in ('constant-copy','reconstruction','endpoint'))
    if len(ordered)!=len(raw) or set(ordered)!=set(raw):
        raise relation.RelationError('EPK canonical authored basis order/multiplicity')
    return ordered


def _raw_linear(terms):
    """Canonical sound generator's authored Int coefficients, without signing."""
    return '['+', '.join(f'({column}, {value})' for column,value in terms)+']'


def _owned_order(source,pair):
    """Exact native seed/bits/comparator/fixed/inverse constructor write order.

    List equality (not quadratic all-pairs inclusion) is checked by the
    generated kernel certificate. Physical ownership is also rechecked here.
    """
    columns=dict(pair['restricted_map'])
    writes=[side[0][0] for side in source['boundary']['published']]
    scalar=source['scalar']
    writes+=list(range(scalar['bit_start'],scalar['bit_start']+252))
    writes += [column for stage in scalar['stages'] for column in (stage['output'],stage['auxiliary'])]
    for item in source['loop']['programs']:
        for stage in item['stages']:
            if stage['kind']=='product':keys=('output','auxiliary')
            elif stage['kind']=='quotient':keys=('quotient','product','auxiliary')
            elif stage['kind']=='linear':keys=('output',)
            else:raise relation.RelationError('EPK proof exact supported owned stage')
            writes.extend(stage[key] for key in keys)
    writes.extend(source['boundary']['inverse_constructor'][key] for key in ('quotient','product','auxiliary'))
    if len(writes)!=len(set(writes)) or set(writes)!=set(pair['source_writes']):
        raise relation.RelationError('EPK proof whole original constructor write coverage/order')
    mapped=[columns[column] for column in writes]
    if len(mapped)!=len(set(mapped)) or set(mapped)!=set(pair['target_writes']):
        raise relation.RelationError('EPK proof whole target owned write coverage/injection')
    return mapped


def _row_source(scope_id,ordinal,block,pair,source_raw,target_raw):
    if not 1<=len(block['indices'])<=CERTIFICATE_ROWS:
        raise relation.RelationError('EPK proof bounded original row certificate')
    row_map=dict(pair['original_row_map']);columns=dict(pair['restricted_map']);actual=[]
    for index in block['indices']:
        if index not in row_map or index not in source_raw:
            raise relation.RelationError('EPK proof original source block coverage')
        target=row_map[index]
        if target not in target_raw:
            raise relation.RelationError('EPK proof original target block coverage')
        mapped=tuple(tuple((columns[c],v) for c,v in side) for side in source_raw[index])
        if mapped!=target_raw[target]:raise relation.RelationError('EPK proof exact row/LC coefficients')
        actual.append(target_raw[target])
    ns=f'RuntimeTransferEpk{scope_id}RenamingRows{ordinal:03d}'
    M=f'ShielddSecurity.RuntimeTransferEpk{scope_id}RenamingMap'
    S='ShielddSecurity.'+block['module']+'.'+block['definition']
    row_linear=_raw_linear if ordinal==126 else linear
    text=f'''import {M}
import ShielddSecurity.{block['module']}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
-- Exact actual physical rows (duplicates retain source-module ordering).
def originalRows : List Nat := {[row_map[i] for i in block['indices']]}
def rawRows : List Row := ['''+',\n'.join('⟨'+row_linear(a)+','+row_linear(b)+'⟩' for a,b in actual)+f''']
theorem exact_rows : rawRows = {S}.map (RowRenaming.row {M}.columns) := by decide
#print axioms exact_rows
end ShielddSecurity.{ns}
'''
    return ns,_signature_audits(text)


def _transport_source(source,pair,blocks,shared,actual_writes):
    scope=pair['scope_id'];ns=f'RuntimeTransferEpk{scope}RenamedCompletion'
    M=f'ShielddSecurity.RuntimeTransferEpk{scope}RenamingMap'
    names=[f'ShielddSecurity.RuntimeTransferEpk{scope}RenamingRows{i:03d}' for i in range(len(blocks))]
    A='ShielddSecurity.RuntimeTransferEpk0Fixed';N='ShielddSecurity.RuntimeTransferEpk0NativeBoundary'
    E=A+'NativeEndpoint';frame=A+'Frame';value=source['scalar']['value']
    target_value=dict(pair['restricted_map'])[value]
    x,y=[side[0][0] for side in source['boundary']['published']]
    tx,ty=[dict(pair['restricted_map'])[c] for c in (x,y)]
    inverse=source['boundary']['inverse_constructor']
    q,p,a=[inverse[key] for key in ('quotient','product','auxiliary')]
    tq=dict(pair['restricted_map'])[q]
    copy=source['checked']['parent']['constant_copy']
    common=f'''{{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (positive : 0 < n) (canonical : n < Scalar.order)
    (meaning : base {target_value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (parameter : ({A}.generator : Group.Point F) = model.coordinates generator)
    (exactOrder : addOrderOf generator = Scalar.order) (linked : base {copy} = base 0)'''
    args='base n positive canonical meaning one four imaginary nonSquare imaginarySquare model generator parameter exactOrder linked'
    out=['import '+N+'\n',*['import '+name+'\n' for name in names],
         f'namespace ShielddSecurity.{ns}\nset_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
         f'def coefficientD : Int := {A}.coefficientD\n',
         f'def pullback {{F : Type}} (base : Nat → F) : Nat → F := fun column => base ({M}.columns column)\n',
         f'def construct {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)\n'
         f'    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) :=\n'
         f'  RowCompletionRenaming.assignment base ({N}.construct (pullback base) model generator n)\n'
         f'    {M}.columns {M}.columns ({N}.totalWrites n)\n',
         f'def writes (n : Nat) : List Nat := ({N}.totalWrites n).map {M}.columns\n',
         f'def actualWrites : List Nat := {actual_writes}\n',
         '''theorem exact_writes (n : Nat) : writes n = actualWrites := by
  change writes 0 = actualWrites
  decide
''']
    chunknames=[]
    for ordinal,chunk in enumerate(source['chunks']):
        start=chunk['metadata']['window_start'];size=chunk['metadata']['window_count']
        members=names[start:start+size];S=f'ShielddSecurity.RuntimeTransferEpk0FixedChunk{start:03d}'
        chunknames.append(f'chunkRows{ordinal}')
        out.append(f'def chunkRows{ordinal} : List Row := ['+','.join(name+'.rawRows' for name in members)+'].flatten\n')
        out.append(f'theorem chunk_exact{ordinal} : chunkRows{ordinal} = {S}.rawRows.map (RowRenaming.row {M}.columns) := by\n'
            f'  simp only [chunkRows{ordinal},{S}.rawRows,{S}.blocks,List.map_flatten,List.map_cons,List.map_nil,'+
            ','.join('← '+name+'.exact_rows' for name in members)+']\n')
    # The basis must be the existing source constructor's whole actual cone.
    # A fixture cannot silently replace it with an arbitrary row list.
    if len(blocks)!=129 or len(names)!=129:
        raise relation.RelationError('EPK proof whole126+canonical+inverse+bindings basis')
    out.append('def fixedRows : List Row := ['+','.join(chunknames+[names[126]+'.rawRows'])+'].flatten\n'
        f'def rawRows : List Row := fixedRows ++ {names[127]}.rawRows ++ {names[128]}.rawRows\n')
    out.append(f'''theorem exact_rows : rawRows =
    ({A}.rawRows ++ {N}.inverseRows ++ {N}.bindingRows).map (RowRenaming.row {M}.columns) := by
  simp only [rawRows,fixedRows,{A}.rawRows,{A}.blocks,List.map_append,List.map_flatten,
    List.map_cons,List.map_nil,'''+','.join('← chunk_exact'+str(i) for i in range(8))+','+
    ','.join('← '+name+'.exact_rows' for name in names[126:])+']\n')
    out.append(f'''theorem scalar_checked : {M}.columns {value} = {target_value} := by decide
theorem protected_checked : {shared}.all (fun column => decide (column ∉ writes 0)) = true := by decide
theorem outside_column {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n column : Nat)
    (outside : column ∉ writes n) : construct base model generator n column = base column :=
  RowCompletionRenaming.assignment_preserves base _ {M}.columns {M}.columns ({N}.totalWrites n) column outside
theorem source_at {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n column : Nat) :
    construct base model generator n ({M}.columns column) =
      {N}.construct (pullback base) model generator n column :=
  RowCompletionRenaming.assignment_at base _ {M}.columns {M}.columns ({N}.totalWrites n)
    column ({M}.inverted column) (by intro item member; exact {M}.inverted item)
    (by intro item outside; exact {N}.outside_total (pullback base) model generator n item outside)
theorem protected_preserved {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n column : Nat)
    (member : column ∈ {shared}) : construct base model generator n column = base column := by
  apply outside_column base model generator n column
  change column ∉ writes 0
  exact of_decide_eq_true (List.all_eq_true.mp protected_checked column member)
theorem outside_eval {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 ∉ writes n) :
    eval (construct base model generator n) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside_column base model generator n term.1 (outside term member)
theorem outside_rows {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) (prior : List Row)
    (previous : Satisfies base prior)
    (outside : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes n) :
    Satisfies (construct base model generator n) prior := by
  intro row member
  change Square (eval (construct base model generator n) row.a) (eval (construct base model generator n) row.b)
  rw [outside_eval base model generator n row.a
    (by intro term present; exact outside row member term (List.mem_append_left _ present)),
    outside_eval base model generator n row.b
    (by intro term present; exact outside row member term (List.mem_append_right _ present))]
  exact previous row member
theorem original_rows_complete {common} : Satisfies (construct base model generator n) rawRows := by
  have scalar : pullback base {value} = (n : F) := by simpa only [pullback,scalar_checked] using meaning
  have unit : pullback base 0 = 1 := by simpa only [pullback,{M}.protected_fixed 0 (by decide)] using one
  have copyLink : pullback base {copy} = pullback base 0 := by
    simpa only [pullback,{M}.protected_fixed {copy} (by decide),{M}.protected_fixed 0 (by decide)] using linked
  have source := {N}.cone_rows_complete (pullback base) n positive canonical scalar unit four imaginary
    nonSquare imaginarySquare model generator parameter exactOrder copyLink
  exact RowCompletionRenaming.complete_rows base _ {M}.columns {M}.columns ({N}.totalWrites n)
    ({A}.rawRows ++ {N}.inverseRows ++ {N}.bindingRows) rawRows exact_rows
    (by intro row member term present; exact {M}.inverted term.1)
    (by intro item member; exact {M}.inverted item)
    (by intro item outside; exact {N}.outside_total (pullback base) model generator n item outside) source
theorem native_published {common} :
    (⟨construct base model generator n {tx},construct base model generator n {ty}⟩ : Group.Point F) =
      model.coordinates (n • generator) := by
  have scalar : pullback base {value} = (n : F) := by simpa only [pullback,scalar_checked] using meaning
  have unit : pullback base 0 = 1 := by simpa only [pullback,{M}.protected_fixed 0 (by decide)] using one
  have copyLink : pullback base {copy} = pullback base 0 := by
    simpa only [pullback,{M}.protected_fixed {copy} (by decide),{M}.protected_fixed 0 (by decide)] using linked
  have published := {E}.published_equal (pullback base) n canonical scalar unit four imaginary nonSquare
    imaginarySquare model generator parameter copyLink
  have point := {E}.native_coordinates (pullback base) n canonical scalar unit four imaginary nonSquare
    imaginarySquare model generator parameter copyLink
  rw [point] at published
  have px := congrArg Group.Point.x published
  have py := congrArg Group.Point.y published
  dsimp only at px py
  have mx : {M}.columns {x} = {tx} := by decide
  have my : {M}.columns {y} = {ty} := by decide
  have ax := source_at base model generator n {x}
  have ay := source_at base model generator n {y}
  rw [mx] at ax
  rw [my] at ay
  have keptX := {N}.outside ({E}.construct (pullback base) model generator n) {x} (by decide)
  have keptY := {N}.outside ({E}.construct (pullback base) model generator n) {y} (by decide)
  apply congrArg₂ Group.Point.mk
  · exact ax.trans (keptX.trans px)
  · exact ay.trans (keptY.trans py)
theorem native_inverse_legal {common} :
    construct base model generator n {tx} * (construct base model generator n {tx})⁻¹ = 1 := by
  have published := native_published {args}
  have coordinate := congrArg Group.Point.x published
  dsimp only at coordinate
  rw [coordinate]
  exact GroupNativeGenerator.canonical_multiple_inverse ({A}.coefficientD : F) model generator exactOrder n positive canonical
theorem inverse_column {common} :
    construct base model generator n {tq} = (construct base model generator n {tx})⁻¹ := by
  have scalar : pullback base {value} = (n : F) := by simpa only [pullback,scalar_checked] using meaning
  have unit : pullback base 0 = 1 := by simpa only [pullback,{M}.protected_fixed 0 (by decide)] using one
  have copyLink : pullback base {copy} = pullback base 0 := by
    simpa only [pullback,{M}.protected_fixed {copy} (by decide),{M}.protected_fixed 0 (by decide)] using linked
  let prior := {E}.construct (pullback base) model generator n
  have published := {E}.published_equal (pullback base) n canonical scalar unit four imaginary nonSquare
    imaginarySquare model generator parameter copyLink
  have point := {E}.native_coordinates (pullback base) n canonical scalar unit four imaginary nonSquare
    imaginarySquare model generator parameter copyLink
  rw [point] at published
  have px := congrArg Group.Point.x published
  dsimp only at px
  have priorOne : prior 0 = 1 := by
    exact (({frame}.outside_column ({E}.seed (pullback base) model generator n) n 0 (by decide)).trans
      ({E}.seed_outside (pullback base) model generator n 0 (by decide))).trans unit
  have quotient := GroupRowCompletion.quotient_value prior [(0,1)] {N}.denominator {N}.remainder {q} {p} {a}
  have mapped : {M}.columns {q} = {tq} := by decide
  have assigned := source_at base model generator n {q}
  rw [mapped] at assigned
  have native := native_published {args}
  have coordinate := congrArg Group.Point.x native
  dsimp only at coordinate
  change {N}.construct (pullback base) model generator n {q} = _ at quotient
  simp only [{N}.denominator,eval,Int.cast_one,one_mul,add_zero,priorOne,px,one_div] at quotient
  exact assigned.trans (quotient.trans (congrArg (fun value : F => value⁻¹) coordinate.symm))
''')
    exports=['exact_writes',*[f'chunk_exact{i}' for i in range(8)],'exact_rows','scalar_checked','protected_checked',
        'outside_column','source_at','protected_preserved','outside_eval','outside_rows','original_rows_complete',
        'native_published','native_inverse_legal','inverse_column']
    out.extend('#print axioms '+name+'\n' for name in exports)
    out.append(f'end ShielddSecurity.{ns}\n')
    return ns,_signature_audits(''.join(out))


def _sequence_adapters(source,pair):
    """Expose a transported cone to the unchanged six-loop composition API.

    These definitions retain the target's exact row certificates and universal
    outside-write theorem. They do not introduce a second construction or a
    precomputed point premise. The strict matcher already joined the native
    generator object and all original operands before this renderer is called.
    """
    scope=pair['scope_id'];stem=f'RuntimeTransferEpk{scope}'
    fixed=stem+'Fixed';boundary=stem+'NativeBoundary';renamed=stem+'RenamedCompletion'
    R='ShielddSecurity.'+renamed;A='ShielddSecurity.'+fixed
    source_fixed='ShielddSecurity.RuntimeTransferEpk0Fixed'
    value=dict(pair['restricted_map'])[source['scalar']['value']]
    copy=source['checked']['parent']['constant_copy']
    rows=f'ShielddSecurity.{stem}RenamingRows'
    fixed_text=f'''import {R}
namespace ShielddSecurity.{fixed}
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
def coefficientD : Int := {source_fixed}.coefficientD
def generator {{F : Type}} [Field F] : Group.Point F := {source_fixed}.generator
def rawRows : List Row := {R}.fixedRows
theorem generator_exact {{F : Type}} [Field F] :
    (generator : Group.Point F) = {source_fixed}.generator := rfl
#print axioms generator_exact
end ShielddSecurity.{fixed}
'''
    common=f'''{{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (positive : 0 < n) (canonical : n < Scalar.order)
    (meaning : base {value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (parameter : ({A}.generator : Group.Point F) = model.coordinates generator)
    (exactOrder : addOrderOf generator = Scalar.order) (linked : base {copy} = base 0)'''
    generic=f'''{{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat)'''
    args='base n positive canonical meaning one four imaginary nonSquare imaginarySquare model generator parameter exactOrder linked'
    boundary_text=f'''import {A}
namespace ShielddSecurity.{boundary}
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
abbrev construct := @{R}.construct
abbrev totalWrites := {R}.writes
def inverseRows : List Row := {rows}127.rawRows
def bindingRows : List Row := {rows}128.rawRows
theorem rows_exact : {A}.rawRows ++ inverseRows ++ bindingRows = {R}.rawRows := rfl
theorem outside_total {generic} (column : Nat) (outside : column ∉ totalWrites n) :
    construct base model generator n column = base column :=
  {R}.outside_column base model generator n column outside
theorem outside_total_eval {generic} (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 ∉ totalWrites n) :
    eval (construct base model generator n) terms = eval base terms :=
  {R}.outside_eval base model generator n terms outside
theorem cone_rows_complete {common} :
    Satisfies (construct base model generator n) ({A}.rawRows ++ inverseRows ++ bindingRows) := by
  rw [rows_exact]
  exact {R}.original_rows_complete {args}
#print axioms rows_exact
#print axioms outside_total
#print axioms outside_total_eval
#print axioms cone_rows_complete
end ShielddSecurity.{boundary}
'''
    return {fixed:_signature_audits(fixed_text),boundary:_signature_audits(boundary_text)}


def generate(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,*,require_renaming=False,
             include_sequence=False):
    """Actual-gated optional optimization; ordinary per-scope fallback retained.

    The initial acceptance is outside the correspondence refusal handler:
    unqualified or mismatched runtime parents never become a fallback success.
    Returned source imports the source0 constructive/native/frame proofs.
    The root must kernel-qualify that exact seed closure before target proofs.
    """
    if type(require_renaming)is not bool or type(include_sequence)is not bool:
        raise relation.RelationError('EPK proof optimization Boolean selector')
    accepted=sequence.plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted)
    try:pairs=[matcher._pair(accepted,i) for i in range(1,6)]
    except relation.RelationError:
        if require_renaming:raise
        result={}
        for i in range(6):result.update(program.generate_scope(qualified_parent,raw_pages,accepted_capsules,
            accepted_roles,extracted,i,include_local=True))
        if include_sequence:
            result['RuntimeTransferEpkSixCompletion']=sequence._render(accepted)
        return dict(mode='full-per-scope',modules=result,ordinary_replays=0,qualification=False,certification=False)
    source=accepted['locals'][0];source_raw=sequence._rows(source);blocks=_blocks(source)
    if {i for block in blocks for i in block['indices']}!=set(source_raw):
        raise relation.RelationError('EPK proof complete source original row footprint')
    result=program.generate_scope(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,0,include_local=True)
    for pair in pairs:
        scope=pair['scope_id'];target_raw=sequence._rows(accepted['locals'][scope])
        name,text=_map_source(pair);result[name]=text
        for ordinal,block in enumerate(blocks):
            name,text=_row_source(scope,ordinal,block,pair,source_raw,target_raw);result[name]=text
        name,text=_transport_source(source,pair,blocks,sorted(set(accepted['protected'])|{6}),_owned_order(source,pair));result[name]=text
        if include_sequence:result.update(_sequence_adapters(source,pair))
    if include_sequence:
        result['RuntimeTransferEpkSixCompletion']=sequence._render(accepted)
    return dict(mode='exact-renaming',modules=result,ordinary_replays=0,qualification=False,certification=False,
        parent_sha256=accepted['parent_sha256'],raw_page_sha256=accepted['raw_page_sha256'],identity=accepted['identity'],
        source_scope=0,target_scopes=list(range(1,6)),scope='Constructive source0 and exact original target row transports; kernel/native caller/full Transfer joins remain separately audited')
