"""Pinned Point::add shared-inverse rows, distinct from fixed-window Div rows.

Every inferred LC comes from a unique original row join. The two final products
must share one inverse, and its materialization must have the actual =1 row.
"""
import hashlib
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_balance_rows import canonical, combine
from .transfer_balance_rows import source_index
from .transfer_fixed_spend import D
from .generate_hash_round import linear, signed, _signature_audits

ALGORITHM='point-add-shared-inverse-v1'


def _boundary(data,accepted):
    from .transfer_rk_addition import boundary
    return boundary(data,accepted)


def _unit(lc):
    return len(lc)==1 and lc[0][0]!=0 and lc[0][1]==1


def _operands(points,v):
    a,b=points['ak'],points['contribution']
    plus=combine(((0,1),),canonical((c,k*D) for c,k in v['xy']))
    minus=combine(((0,1),),canonical((c,k*D) for c,k in v['xy']),-1)
    return dict(xx=(a[0],b[0]),yy=(a[1],b[1]),xy=(v['xx'],v['yy']),
        denominator=(plus,minus),inverseProduct=(v['inverse'],v['denominator']),
        cross0=(a[0],b[1]),cross1=(a[1],b[0]),
        adjustedX=(combine(v['cross0'],v['cross1']),minus),
        outputX=(v['adjustedX'],v['inverse']),
        adjustedY=(combine(v['yy'],v['xx']),plus),outputY=(v['adjustedY'],v['inverse']))


def _infer_inverse(stream,obj,adjusted,outputs):
    """Bounded row join with known left/output; both axes share one unit LC."""
    copy=obj['constant_copy'];records={};first=[{},{}];second=[{},{}]
    def retain(table,inverse,index,row):
        table.setdefault(inverse,[]).append(index);records[index]=row
        if sum(map(len,table.values()))>256:raise relation.RelationError('RK inverse candidate bound')
    def observe(row):
        a,b=(canonical((0 if c==copy else c,int(k,16)) for c,k in row[key]) for key in ('a','b'))
        for axis,(left,out) in enumerate(zip(adjusted,outputs)):
            if _unit(b):
                for inverse in (combine(left,a,-1),combine(left,a)):
                    if _unit(inverse) and inverse not in (left,out):retain(first[axis],inverse,row['row'],row)
            aux=combine(b,out,-4);inverse=combine(a,left,-1)
            if _unit(aux) and _unit(inverse) and inverse not in (left,out):
                retain(second[axis],inverse,row['row'],row)
    identity=relation.inspect(stream,expected_relation=obj['relation_digest'],row_observer=observe)
    if identity['domain_size']!=obj['domain_size'] or identity['stored_rows']!=obj['full_rows']:
        raise relation.RelationError('RK inverse ordinary shape changed')
    normal={i:tuple(canonical((0 if c==copy else c,int(k,16)) for c,k in row[key]) for key in ('a','b')) for i,row in records.items()}
    candidates=[]
    for inverse in set(first[0])&set(second[0])&set(first[1])&set(second[1]):
        joins=[]
        for axis in range(2):
            matches=[]
            for x in first[axis][inverse]:
                for y in second[axis][inverse]:
                    if x==y:continue
                    try: arithmetic.product_certificate(adjusted[axis],inverse,outputs[axis],{x:normal[x],y:normal[y]})
                    except relation.RelationError:continue
                    matches.append((x,y))
            joins.append(list(dict.fromkeys(matches)))
        if all(len(j)==1 for j in joins):candidates.append((inverse,joins[0][0]+joins[1][0]))
        elif all(joins):raise relation.RelationError('RK endpoint product row ambiguity')
    if len(candidates)!=1:raise relation.RelationError('RK endpoints require one exact shared inverse')
    inverse,indices=candidates[0]
    return dict(identity=identity,inverse=inverse,selected_rows=[records[i] for i in sorted(set(indices))])


def extract(data,accepted,open_stream):
    obj,points=_boundary(data,accepted);a,b=points['ak'],points['contribution'];stages=[];v={}
    def infer(operands):
        with open_stream() as stream:
            result=arithmetic.infer_product_outputs(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],operands,obj['constant_copy'],require_unit_output=True)
        stages.append(result);v.update({name:item['output'] for name,item in result['products'].items()})
    infer(dict(xx=(a[0],b[0]),yy=(a[1],b[1]),cross0=(a[0],b[1]),cross1=(a[1],b[0])))
    infer(dict(xy=(v['xx'],v['yy'])))
    plus=combine(((0,1),),canonical((c,k*D) for c,k in v['xy']))
    minus=combine(((0,1),),canonical((c,k*D) for c,k in v['xy']),-1)
    infer(dict(denominator=(plus,minus),adjustedX=(combine(v['cross0'],v['cross1']),minus),adjustedY=(combine(v['yy'],v['xx']),plus)))
    with open_stream() as stream:inverse=_infer_inverse(stream,obj,(v['adjustedX'],v['adjustedY']),points['computed'])
    stages.append(inverse);v['inverse']=inverse['inverse'];v['outputX'],v['outputY']=points['computed']
    outline=lambda lc:canonical((obj['constant_copy'] if c==0 else c,k) for c,k in lc)
    required={(canonical([(0,1),(obj['constant_copy'],-1)]),()):['constant-copy']}
    left,right=v['inverse'],v['denominator']
    with open_stream() as stream:
        final=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],required,
            [('inverse',outline(combine(left,right,-1)),outline(combine(left,right)),None,outline(((0,1),)))],[],label='RK shared inverse')
    stages.append(final)
    if any(stage['identity']!=stages[0]['identity'] for stage in stages):raise relation.RelationError('RK ordinary passes changed identity/shape')
    rows={r['row']:r for stage in stages for r in stage['selected_rows']}
    normal={i:tuple(canonical((0 if c==obj['constant_copy'] else c,int(k,16)) for c,k in r[key]) for key in ('a','b')) for i,r in rows.items()}
    inv=arithmetic.quotient_certificate(((0,1),),v['denominator'],v['inverse'],normal)
    v['inverseProduct']=inv['output']
    result=dict(algorithm=ALGORITHM,identity=stages[0]['identity'],metadata_sha256=hashlib.sha256(data).hexdigest(),
        intermediates={name:[[c,k] for c,k in terms] for name,terms in v.items()},selected_rows=[rows[i] for i in sorted(rows)],
        scope='exact original Point::add shared-inverse rows; kernel/native/full Transfer joins remain open')
    selection(data,accepted,result)
    return result


def selection(data,accepted,extracted):
    obj,points=_boundary(data,accepted)
    if not isinstance(extracted,dict) or extracted.get('algorithm')!=ALGORITHM:raise relation.RelationError('RK shared inverse algorithm')
    raw,normal=arithmetic.normalize_selection(extracted,obj,hashlib.sha256(data).hexdigest());items=extracted.get('intermediates')
    names={'xx','yy','xy','denominator','inverse','inverseProduct','cross0','cross1','adjustedX','outputX','adjustedY','outputY'}
    if not isinstance(items,dict) or set(items)!=names:raise relation.RelationError('RK shared inverse intermediate shape')
    v={}
    for name,terms in items.items():
        if not isinstance(terms,list) or len(terms)>4096:raise relation.RelationError('RK shared inverse LC bound')
        parsed=[];last=-1
        for term in terms:
            if not isinstance(term,list) or len(term)!=2:raise relation.RelationError('RK shared inverse LC term')
            c=relation.natural(term[0],obj['domain_size']);k=term[1]
            if c<=last or type(k)is not int or not 0<k<relation.MODULUS:raise relation.RelationError('RK shared inverse noncanonical LC')
            parsed.append((c,k));last=c
        v[name]=tuple(parsed)
    if not _unit(v['inverse']) or (v['outputX'],v['outputY'])!=points['computed']:
        raise relation.RelationError('RK shared inverse/endpoints changed')
    operands=_operands(points,v);certificates={name:arithmetic.product_certificate(*pair,v[name],normal) for name,pair in operands.items()}
    inverse=arithmetic.quotient_certificate(((0,1),),v['denominator'],v['inverse'],normal)
    if inverse['output']!=v['inverseProduct']:raise relation.RelationError('RK inverse assertion product changed')
    covered={i for c in certificates.values() for i in c['rows']}|set(inverse['rows'])
    constants={i for i,row in raw.items() if row==(canonical([(0,1),(obj['constant_copy'],-1)]),())}
    if len(constants)!=1 or covered|constants!=set(raw):raise relation.RelationError('RK original row coverage is not exact')
    # Refuse ambiguous retained encodings rather than silently picking a pair.
    for name,(left,right) in operands.items():
        c=certificates[name]
        if c['kind']=='product':
            difference=combine(left,right,-1);plus=combine(left,right)
            pairs=[(x,y) for x,(a,aux) in normal.items() if a in (difference,canonical((col,-k) for col,k in difference))
                   for y,row in normal.items() if x!=y and row==(plus,combine(aux,v[name],4))]
            if len(pairs)!=1:raise relation.RelationError('RK retained product ambiguity: '+name)
    return obj,points,raw,normal,v,operands,certificates,[inverse]


def generate(data,accepted,extracted):
    from .generate_transfer_fixed_spend import _product_completion_sources
    obj,points,raw,normal,v,operands,certificates,_=selection(data,accepted,extracted);copy=obj['constant_copy']
    out=['import ShielddSecurity.GroupFixedWindows\nimport ShielddSecurity.TransferSubgroup\nimport ShielddSecurity.CompilerCompletion\nimport ShielddSecurity.ScalarRows\nimport ShielddSecurity.ScalarComparisonBounds\n',
        'namespace ShielddSecurity.RuntimeTransferRkAddition\nset_option maxHeartbeats 500000\n',
        f'def modulus : Nat := {relation.MODULUS}\ndef coefficientD : Int := {signed(D)}\n',
        'def originalRows : List Nat := '+str(sorted(raw))+'\n',
        'def rawRows : List Row := ['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(raw))+']\n',
        f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n',
        f'theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n',
        '''theorem fourNonzero {F : Type} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
'''];exports=['constantLink','fourNonzero']
    for name,pair in operands.items():
        c=certificates[name];source,names=_product_completion_sources(name,*pair,v[name],c,raw,normal,copy)
        out.append(source);exports+=names
        for suffix,lc in (('left',pair[0]),('right',pair[1]),('output',v[name])):out.append(f'def {name}_{suffix} : Linear := {linear(lc)}\n')
        left,right=(name+'_right',name+'_left') if c.get('swapped') else (name+'_left',name+'_right')
        datum='.product '+linear(c['auxiliary']) if c['kind']=='product' else '.square' if c['kind']=='square' else ('.foldedLeft ' if c['kind']=='folded_left' else '.foldedRight ')+f'({signed(c["coefficient"])} : Int)'
        out.append(f'''theorem {name}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {name}_output = eval rho {name}_left * eval rho {name}_right := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product := ScalarRows.checked_product_sound rho one (fourNonzero (F := F)) rows normalized
    {left} {right} {name}_output ({datum}) (by decide)
  simpa only [mul_comm] using product
''');exports.append(name+'_sound')
    for name,point in points.items():out.append(f'def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(point[0])},eval rho {linear(point[1])}⟩\n')
    for name,lc in (('inverse',v['inverse']),('plus',operands['denominator'][0]),('minus',operands['denominator'][1]),('crossSum',operands['adjustedX'][0]),('diagonalSum',operands['adjustedY'][0])):out.append(f'def {name} : Linear := {linear(lc)}\n')
    out.append(f'''theorem inverse_equation {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho denominator_output * eval rho inverse = 1 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have equal := ScalarComparisonBounds.checked_equality rho rows normalized inverseProduct_output [(0,1)] (by decide)
  have product := inverseProduct_sound rho one satisfied
  have unit : eval rho [(0,1)] = 1 := by simp [eval,one]
  rw [product,unit] at equal
  simpa only [inverseProduct_left,inverseProduct_right,denominator_output,inverse,mul_comm]
    using equal
theorem actual_addition_affine {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    computed rho = Group.affineAdd (coefficientD : F) (ak rho) (contribution rho) := by
''')
    for name in operands:out.append(f'  have {name}Value := {name}_sound rho one satisfied\n')
    for name,lc,target in (
        ('plus','[(0,1)] ++ scaleLinear coefficientD xy_output','1+(coefficientD : F)*eval rho xy_output'),
        ('minus','[(0,1)] ++ scaleLinear (-coefficientD) xy_output','1-(coefficientD : F)*eval rho xy_output'),
        ('crossSum','cross0_output ++ cross1_output','eval rho cross0_output + eval rho cross1_output'),
        ('diagonalSum','yy_output ++ xx_output','eval rho yy_output + eval rho xx_output')):
        out.append(f'''  have {name}Value : eval rho {name} = {target} := by
    have checked := Compiler.canonical_equal rho {name} ({lc}) (by decide)
    simpa only [eval_append,eval_scale,eval,one,Int.cast_one,Int.cast_neg,one_mul,add_zero,
      sub_eq_add_neg,neg_one_mul,neg_mul] using checked
''')
    for name,axis0,axis1 in (('xx','x','x'),('yy','y','y'),('cross0','x','y'),('cross1','y','x')):
        out.append(f'  change eval rho {name}_output = (ak rho).{axis0} * (contribution rho).{axis1} at {name}Value\n')
    out.append('''  change eval rho xy_output = eval rho xx_output * eval rho yy_output at xyValue
  rw [xxValue,yyValue] at xyValue
  have deltaValue : (coefficientD : F)*eval rho xy_output =
      Group.delta (coefficientD : F) (ak rho) (contribution rho) := by
    rw [xyValue]
    unfold Group.delta
    ring
  have plusSemantic : eval rho plus = 1+Group.delta (coefficientD : F) (ak rho) (contribution rho) := by
    rw [plusValue,deltaValue]
  have minusSemantic : eval rho minus = 1-Group.delta (coefficientD : F) (ak rho) (contribution rho) := by
    rw [minusValue,deltaValue]
  have crossSemantic : eval rho crossSum = Group.cross (ak rho) (contribution rho) := by
    rw [crossSumValue,cross0Value,cross1Value]
    rfl
  have diagonalSemantic : eval rho diagonalSum = Group.diagonal (ak rho) (contribution rho) := by
    rw [diagonalSumValue,yyValue,xxValue]
    rfl
  change eval rho denominator_output = eval rho plus * eval rho minus at denominatorValue
  change eval rho adjustedX_output = eval rho crossSum * eval rho minus at adjustedXValue
  change eval rho adjustedY_output = eval rho diagonalSum * eval rho plus at adjustedYValue
  change (computed rho).x = eval rho adjustedX_output * eval rho inverse at outputXValue
  change (computed rho).y = eval rho adjustedY_output * eval rho inverse at outputYValue
  have inverseRow := inverse_equation rho one satisfied
  rw [denominatorValue,plusSemantic,minusSemantic] at inverseRow
  rw [adjustedXValue,crossSemantic,minusSemantic] at outputXValue
  rw [adjustedYValue,diagonalSemantic,plusSemantic] at outputYValue
  exact TransferSubgroup.shared_inverse_affine (coefficientD : F) (eval rho inverse)
    (ak rho) (contribution rho) (computed rho) inverseRow outputXValue outputYValue
''')
    affine_source=''.join(out)
    affine_source=affine_source[affine_source.index('theorem actual_addition_affine'):]
    row_source=affine_source.replace('theorem actual_addition_affine','theorem actual_addition_rows').replace(
        'computed rho = Group.affineAdd (coefficientD : F) (ak rho) (contribution rho) := by',
        'TransferOwnership.AddEquations (coefficientD : F) (ak rho) (contribution rho) (computed rho) := by').replace(
        '''  exact TransferSubgroup.shared_inverse_affine (coefficientD : F) (eval rho inverse)
    (ak rho) (contribution rho) (computed rho) inverseRow outputXValue outputYValue''',
        '''  have equations := Group.shared_inverse_rows (coefficientD : F) (eval rho inverse)
    (ak rho) (contribution rho) (computed rho) inverseRow outputXValue outputYValue
  exact ⟨equations.1.trans (by unfold Group.cross; ring),equations.2⟩''')
    # The preceding fragment includes only the affine theorem, not inverse_equation.
    row_source=row_source[row_source.index('theorem actual_addition_rows'):]
    out.append(row_source)
    out.append('''theorem actual_add_coordinates {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (actionKey fixedContribution : J)
    (akRole : ak rho = model.coordinates actionKey)
    (contributionRole : contribution rho = model.coordinates fixedContribution)
    (satisfied : Satisfies rho rawRows) :
    computed rho = model.coordinates (actionKey+fixedContribution) := by
  have output := actual_addition_affine rho one satisfied
  rw [akRole,contributionRole] at output
  exact output.trans (model.addition actionKey fixedContribution).symm
''')
    exports+=['inverse_equation','actual_addition_affine','actual_addition_rows','actual_add_coordinates']
    out.extend('#print axioms '+name+'\n' for name in exports);out.append('end ShielddSecurity.RuntimeTransferRkAddition\n')
    return _signature_audits(''.join(out))


def completion_plan(data,accepted,extracted):
    obj,points,raw,normal,v,operands,certificates,inverses=selection(data,accepted,extracted)
    computed={source_index(ref['source']) for ref in obj['spend']['computed']};kept={0,obj['constant_copy']}
    for handle,lc in accepted['observed'].items():
        if handle not in computed:kept.update(c for c,_ in lc)
    stages=[]
    for name in ('xx','yy','xy','denominator','inverse','cross0','cross1','adjustedX','outputX','adjustedY','outputY'):
        if name=='inverse':
            certificate=inverses[0];transport=dict(normal)
            assertion=certificate['rows'][-1]
            positive=(combine(certificate['output'],certificate['numerator'],-1),())
            negative=(canonical((col,-k) for col,k in positive[0]),())
            if normal[assertion] not in (positive,negative):raise relation.RelationError('RK inverse assertion orientation')
            transport[assertion]=positive
            c=arithmetic.completion_certificate(certificate,transport)
            if c is None:raise relation.RelationError('RK shared inverse unsupported inverse construction')
            stages.append(dict(kind='quotient',role=name,assertion_negative=normal[assertion]==negative,**c))
        else:
            c=arithmetic.product_completion_certificate(*operands[name],v[name],certificates[name],normal)
            if c is None:raise relation.RelationError('RK shared inverse unsupported product construction: '+name)
            stages.append(dict(kind='product',role=name,**c))
    prior=set();owned=set();covered=set()
    for stage in stages:
        writes={stage['output'],stage['auxiliary']} if stage['kind']=='product' else {stage['quotient'],stage['product'],stage['auxiliary']}
        if writes&(kept|prior|owned):raise relation.RelationError('RK shared inverse writes alias kept/prior support: '+stage['role'])
        if covered&set(stage['rows']):raise relation.RelationError('RK shared inverse row ownership overlaps')
        owned.update(writes);covered.update(stage['rows'])
        for i in stage['rows']:
            for lc in normal[i]:prior.update(c for c,_ in lc)
    constant=next(i for i,row in raw.items() if row==(canonical([(0,1),(obj['constant_copy'],-1)]),()))
    if covered|{constant}!=set(raw):raise relation.RelationError('RK shared inverse original row coverage')
    return dict(stages=stages,kept=sorted(kept),writes=sorted(owned),constant_row=constant,original_rows=sorted(raw))


def generate_completion(data,accepted,extracted):
    plan=completion_plan(data,accepted,extracted)
    obj,points,raw,normal,v,operands,certificates,_=selection(data,accepted,extracted);copy=obj['constant_copy']
    steps=[];expected={};emitted=[]
    for stage in plan['stages']:
        if stage['kind']=='product':
            l,r,rem=(linear(stage[k]) for k in ('left','right','remainder'));o,u=stage['output'],stage['auxiliary']
            steps.append(f'.compiler (.product {l} {r} {rem} {o} {u})')
            rows=[f'⟨Compiler.subtract {l} {r},[({u},1)]⟩',f'⟨{l} ++ {r},[({u},1)] ++ scaleLinear 4 ([({o},1)] ++ {rem})⟩']
        else:
            n,d,rem=(linear(stage[k]) for k in ('numerator','denominator','remainder'));q,p,u=(stage[k] for k in ('quotient','product','auxiliary'))
            steps.append(f'.quotient {n} {d} {rem} {q} {p} {u}')
            rows=[f'⟨Compiler.subtract [({q},1)] {d},[({u},1)]⟩',
                  f'⟨[({q},1)] ++ {d},[({u},1)] ++ scaleLinear 4 ([({p},1)] ++ {rem})⟩',
                  f'⟨Compiler.subtract ([({p},1)] ++ {rem}) {n},[]⟩']
        expected.update(zip(stage['rows'],rows));emitted+=rows
    expected[plan['constant_row']]='⟨Compiler.subtract [] [],[]⟩';emitted.append(expected[plan['constant_row']])
    steps.append('.compiler (.equal [] [])')
    out=['''import ShielddSecurity.GroupCircuitOrder
import ShielddSecurity.ScalarRows
namespace ShielddSecurity.RuntimeTransferRkAdditionCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
''',f'def modulus : Nat := {relation.MODULUS}\ndef coefficientD : Int := {signed(D)}\n',
        f'def kept : List Nat := {plan["kept"]}\ndef completionWrites : List Nat := {plan["writes"]}\n',
        'def rawRows : List Row := ['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(raw))+']\n',
        'def productStages : List GroupCircuitCompletion.Step := ['+',\n'.join(steps[:4])+']\n',
        'def completionSteps : List GroupCircuitCompletion.Step := productStages ++ ['+',\n'.join(steps[4:])+']\n',
        'def expectedRows : List Row := ['+',\n'.join(emitted)+']\n',
        '''theorem emitted_exact : GroupCircuitCompletion.emitted completionSteps = expectedRows := rfl
def productAssignment {F : Type} [Field F] (rho : Nat → F) := GroupCircuitCompletion.run rho productStages
def completeAssignment {F : Type} [Field F] (rho : Nat → F) := GroupCircuitCompletion.run rho completionSteps
theorem completion_ordered : GroupCircuitCompletion.Topological kept [] completionSteps :=
  GroupCircuitOrder.checked_order kept [] completionSteps (by decide)
theorem product_kept {F : Type} [Field F] (rho : Nat → F) (column : Nat) (member : column ∈ kept) :
    productAssignment rho column = rho column :=
  GroupCircuitCompletion.run_preserves rho productStages kept []
    (GroupCircuitOrder.checked_order kept [] productStages (by decide)) column member
theorem product_eval_kept {F : Type} [Field F] (rho : Nat → F) (terms : Linear)
    (included : ∀ term ∈ terms, term.1 ∈ kept) : eval (productAssignment rho) terms = eval rho terms := by
  apply eval_agrees
  intro term member
  exact product_kept rho term.1 (included term member)
''']
    for name,point in (('actionKey',points['ak']),('fixedContribution',points['contribution'])):
        out.append(f'def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(point[0])},eval rho {linear(point[1])}⟩\n')
    out.append(f'def denominator : Linear := {linear(v["denominator"])}\n')
    out.append('''theorem product_inputs_preserved {F : Type} [Field F] (rho : Nat → F) :
    actionKey (productAssignment rho) = actionKey rho ∧ fixedContribution (productAssignment rho) = fixedContribution rho := by
  constructor
''')
    for _,point in (('actionKey',points['ak']),('fixedContribution',points['contribution'])):
        out.append('  · apply congrArg₂ Group.Point.mk\n')
        for lc in point:out.append(f'    · exact product_eval_kept rho {linear(lc)} (by simp [kept])\n')
    out.append('''theorem constructed_denominator {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (productAssignment rho) denominator =
      (1+Group.delta (coefficientD : F) (actionKey rho) (fixedContribution rho)) *
        (1-Group.delta (coefficientD : F) (actionKey rho) (fixedContribution rho)) := by
  let built := productAssignment rho
  have oneBuilt : built 0 = 1 := (product_kept rho 0 (by decide)).trans one
  have satisfied := GroupCircuitCompletion.run_constructs rho productStages kept
    (GroupCircuitOrder.checked_order kept [] productStages (by decide))
    (by exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro⟩)
''')
    for name,stage in zip(('xx','yy','xy','denominator'),plan['stages'][:4]):
        out.append(f'''  have {name}Value := ScalarRows.checked_product_sound built oneBuilt four
    (GroupCircuitCompletion.emitted productStages) satisfied
    {linear(stage['left'])} {linear(stage['right'])} {linear(v[name])}
    (.product [({stage['auxiliary']},1)]) (by decide)
''')
    for name,axis in (('xx','x'),('yy','y')):
        out.append(f'''  have {name}Semantic : eval built {linear(v[name])} = (actionKey built).{axis} * (fixedContribution built).{axis} := by
    simpa only [actionKey,fixedContribution,mul_comm] using {name}Value
''')
    out.append(f'''  have xySemantic : eval built {linear(v['xy'])} =
      ((actionKey built).x*(fixedContribution built).x) * ((actionKey built).y*(fixedContribution built).y) := by
    have joined : eval built {linear(v['xy'])} = eval built {linear(v['xx'])} * eval built {linear(v['yy'])} := by
      simpa only [mul_comm] using xyValue
    rw [xxSemantic,yySemantic] at joined
    exact joined
  have deltaSemantic : (coefficientD : F)*eval built {linear(v['xy'])} =
      Group.delta (coefficientD : F) (actionKey built) (fixedContribution built) := by
    rw [xySemantic]
    unfold Group.delta
    ring
''')
    for name,sign,lc in (('plus','+',operands['denominator'][0]),('minus','-',operands['denominator'][1])):
        scale='coefficientD' if sign=='+' else '(-coefficientD)'
        out.append(f'''  have {name}Semantic : eval built {linear(lc)} =
      1 {sign} Group.delta (coefficientD : F) (actionKey built) (fixedContribution built) := by
    have checked := Compiler.canonical_equal built {linear(lc)}
      ([(0,1)] ++ scaleLinear {scale} {linear(v['xy'])}) (by decide)
    have unit : eval built [(0,1)] = 1 := by simp [eval,oneBuilt]
    simp only [eval_append,eval_scale,unit,Int.cast_neg,neg_mul] at checked
    rw [checked,deltaSemantic] <;> ring
''')
    out.append(f'''  have joined : eval built denominator = eval built {linear(operands['denominator'][0])} * eval built {linear(operands['denominator'][1])} := by
    simpa only [denominator,mul_comm] using denominatorValue
  rw [plusSemantic,minusSemantic] at joined
  have inputs := product_inputs_preserved rho
  rw [inputs.1,inputs.2] at joined
  exact joined
theorem completion_legal {{F : Type}} [Field F] (rho : Nat → F)
    (nonzero : eval (productAssignment rho) denominator ≠ 0) :
    GroupCircuitCompletion.Legal rho completionSteps := by
  change True ∧ True ∧ True ∧ True ∧ (eval (productAssignment rho) denominator ≠ 0) ∧
    True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((0 : F) = 0) ∧ True
  exact ⟨True.intro,True.intro,True.intro,True.intro,nonzero,
    True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,rfl,True.intro⟩
theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈ GroupCircuitCompletion.emitted completionSteps,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  rw [emitted_exact]
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in raw)+'\n')
    for i in sorted(raw):out.append(f'  · exact ⟨{expected[i]}, by decide, by decide, by decide⟩\n')
    out.append(f'''theorem actual_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (linked : rho {copy} = rho 0)
      (nonzero : eval (productAssignment rho) denominator ≠ 0) :
    Satisfies (completeAssignment rho) rawRows ∧ (∀ column ∈ kept, completeAssignment rho column = rho column) := by
  let built := completeAssignment rho
  have completed := GroupCircuitCompletion.run_constructs rho completionSteps kept
    completion_ordered (completion_legal rho nonzero)
  have preserves := GroupCircuitCompletion.run_preserves rho completionSteps kept [] completion_ordered
  have copyBuilt : built {copy} = built 0 := by
    exact (preserves {copy} (by decide)).trans (linked.trans (preserves 0 (by decide)).symm)
  constructor
  · intro actual member
    obtain ⟨expected,included,left,right⟩ := original_coverage actual member
    have sound := completed expected included
    change Square (eval built expected.a) (eval built expected.b) at sound
    rcases left with positive | negative
    · rw [← Compiler.canonical_equal built _ _ positive,
        ← Compiler.canonical_equal built _ _ right] at sound
      simpa only [Compiler.eval_unoutline built {copy} _ copyBuilt] using sound
    · have negated : Square (eval built (scaleLinear (-1) expected.a)) (eval built expected.b) := by
        simpa [Square,eval_scale] using sound
      rw [← Compiler.canonical_equal built _ _ negative,
        ← Compiler.canonical_equal built _ _ right] at negated
      simpa only [Compiler.eval_unoutline built {copy} _ copyBuilt] using negated
  · exact preserves
theorem actual_curve_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (linked : rho {copy} = rho 0) (keyValid : Group.OnCurve (coefficientD : F) (actionKey rho))
    (contributionValid : Group.OnCurve (coefficientD : F) (fixedContribution rho)) :
    Satisfies (completeAssignment rho) rawRows ∧ (∀ column ∈ kept, completeAssignment rho column = rho column) := by
  have denominatorValue := constructed_denominator rho one four
  have legal := Group.denominators_nonzero (coefficientD : F) imaginary nonSquare imaginarySquare
    (actionKey rho) (fixedContribution rho) keyValid contributionValid
  apply actual_rows_complete rho linked
  rw [denominatorValue]
  exact mul_ne_zero legal.1 legal.2
''')
    exports=['emitted_exact','completion_ordered','product_kept','product_eval_kept','product_inputs_preserved',
             'constructed_denominator','completion_legal','original_coverage','actual_rows_complete','actual_curve_rows_complete']
    out.extend('#print axioms '+n+'\n' for n in exports);out.append('end ShielddSecurity.RuntimeTransferRkAdditionCompletion\n')
    return _signature_audits(''.join(out))
