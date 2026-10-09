"""Actual AK plus fixed-contribution rows, inferred from exact operand LCs.

No intermediate source observations are invented. Unique materialized product
LCs are derived from ordinary row pairs, then joined to both quotient/assertion
rows with the captured computed-point endpoints. All passes replay the full
ordinary relation. A hash records identity; the row equations supply meaning.
"""
import hashlib
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index
from .transfer_fixed_spend import D
from .generate_hash_round import linear, signed, _signature_audits
from .transfer_ownership import generate_quotient_boundaries
from .generate_transfer_fixed_spend import _completion_sources, _product_completion_sources


def boundary(data,accepted_roles):
    obj=relation.record(data)
    if not isinstance(accepted_roles,dict) or obj!=accepted_roles.get('metadata'):
        raise relation.RelationError('RK addition requires matching accepted authorization roles')
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],2048,'RK addition')
    if observed!=accepted_roles.get('observed'):
        raise relation.RelationError('RK addition shared source LCs changed')
    spend=obj['spend']
    points={name:tuple(observed[source_index(v['source'])] for v in spend[name])
            for name in ('ak','contribution','computed')}
    return obj,points


def _extract_legacy(data,accepted_roles,open_stream):
    """Three sequential bounded full-row passes; open_stream returns a file."""
    obj,points=boundary(data,accepted_roles)
    left,right=points['ak'],points['contribution'];copy=obj['constant_copy']
    operands={'xx':(left[0],right[0]),'yy':(left[1],right[1]),
              'sum':(combine(*left),combine(*right))}
    def infer(values):
        with open_stream() as stream:
            return arithmetic.infer_product_outputs(stream,obj['relation_digest'],obj['domain_size'],
                                                     obj['full_rows'],values,copy)
    first=infer(operands);values={name:item['output'] for name,item in first['products'].items()}
    second=infer({'xy':(values['xx'],values['yy'])});values['xy']=second['products']['xy']['output']
    operands['xy']=(values['xx'],values['yy'])
    numerators=[combine(combine(values['sum'],values['xx'],-1),values['yy'],-1),combine(values['yy'],values['xx'])]
    denominators=[combine(((0,1),),canonical((c,v*D) for c,v in values['xy'])),
                  combine(((0,1),),canonical((c,v*D) for c,v in values['xy']),-1)]
    outlined=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']};products=[];squares=[]
    for axis,(n,d,q) in enumerate(zip(numerators,denominators,points['computed'])):
        role='quotient'+str(axis)
        folded=next(((s,o) for s,o in ((d,q),(q,d)) if not s or len(s)==1 and s[0][0]==0),None)
        if folded:
            s,o=folded;coefficient=s[0][1] if s else 0
            equation=combine(canonical((c,v*coefficient) for c,v in o),n,-1)
            if equation:required.setdefault((outlined(equation),()),[]).append(role)
        elif d==q:squares.append((role,outlined(q),outlined(n)))
        else:products.append((role,outlined(combine(q,d,-1)),outlined(combine(q,d)),None,outlined(n)))
    with open_stream() as stream:
        third=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
                                           required,products,squares,label='RK addition')
    if not first['identity']==second['identity']==third['identity']:
        raise relation.RelationError('RK addition ordinary passes changed identity/shape')
    rows={row['row']:row for stage in (first,second,third) for row in stage['selected_rows']}
    result=dict(identity=first['identity'],metadata_sha256=hashlib.sha256(data).hexdigest(),
                selected_rows=[rows[i] for i in sorted(rows)],
                intermediates={name:[[c,v] for c,v in value] for name,value in values.items()},
                scope='unique actual AK/contribution addition rows only; kernel/native/full Transfer qualification open')
    _selection(data,accepted_roles,result)
    return result


def extract(data,accepted_roles,open_stream):
    """Exact pinned generic Point::add, rather than the fixed-window Div shape."""
    from . import transfer_rk_point_add
    return transfer_rk_point_add.extract(data,accepted_roles,open_stream)


def _selection(data,accepted_roles,extracted):
    if isinstance(extracted,dict) and extracted.get('algorithm')=='point-add-shared-inverse-v1':
        from . import transfer_rk_point_add
        return transfer_rk_point_add.selection(data,accepted_roles,extracted)
    obj,points=boundary(data,accepted_roles)
    raw,normalized=arithmetic.normalize_selection(extracted,obj,hashlib.sha256(data).hexdigest())
    intermediates=extracted.get('intermediates')
    if not isinstance(intermediates,dict) or set(intermediates)!={'xx','yy','sum','xy'}:
        raise relation.RelationError('RK addition intermediate LC shape')
    values={}
    for name,terms in intermediates.items():
        if not isinstance(terms,list) or len(terms)>4096:raise relation.RelationError('RK addition LC bound')
        last=-1;parsed=[]
        for term in terms:
            if not isinstance(term,list) or len(term)!=2:raise relation.RelationError('RK addition LC term')
            c=relation.natural(term[0],obj['domain_size']);v=term[1]
            if c<=last or type(v)is not int or not 0<v<relation.MODULUS:raise relation.RelationError('RK addition noncanonical LC')
            last=c;parsed.append((c,v))
        values[name]=tuple(parsed)
    left,right=points['ak'],points['contribution']
    operands={'xx':(left[0],right[0]),'yy':(left[1],right[1]),
              'sum':(combine(*left),combine(*right)),'xy':(values['xx'],values['yy'])}
    certificates={name:arithmetic.product_certificate(*operands[name],values[name],normalized) for name in values}
    numerators=[combine(combine(values['sum'],values['xx'],-1),values['yy'],-1),combine(values['yy'],values['xx'])]
    denominators=[combine(((0,1),),canonical((c,v*D) for c,v in values['xy'])),
                  combine(((0,1),),canonical((c,v*D) for c,v in values['xy']),-1)]
    quotients=[arithmetic.quotient_certificate(n,d,q,normalized)
               for n,d,q in zip(numerators,denominators,points['computed'])]
    return obj,points,raw,normalized,values,operands,certificates,quotients


def generate(data,accepted_roles,extracted):
    if isinstance(extracted,dict) and extracted.get('algorithm')=='point-add-shared-inverse-v1':
        from . import transfer_rk_point_add
        return transfer_rk_point_add.generate(data,accepted_roles,extracted)
    obj,points,raw,normalized,values,operands,certificates,quotients=_selection(data,accepted_roles,extracted)
    copy=obj['constant_copy'];Q='ShielddSecurity.RuntimeTransferRkAdditionDiv'
    qsource=generate_quotient_boundaries(dict(outline=copy,rows=raw,
        certificates=[dict(c,role='quotient'+str(i)) for i,c in enumerate(quotients)]),
        hashlib.sha256(data).hexdigest(),obj['relation_digest'],namespace='RuntimeTransferRkAdditionDiv')
    out=['import ShielddSecurity.GroupFixedWindows\nimport ShielddSecurity.GroupRowCompletion\nimport ShielddSecurity.CompilerCompletion\nimport ShielddSecurity.ScalarRows\n',
         qsource.removeprefix('import ShielddSecurity.Compiler\n'),
         'namespace ShielddSecurity.RuntimeTransferRkAddition\nset_option maxHeartbeats 500000\n',
         f'def modulus : Nat := {relation.MODULUS}\ndef coefficientD : Int := {signed(D)}\n',
         'def originalRows : List Nat := '+str(sorted(raw))+'\n',
         f'def rawRows : List Row := {Q}.rawRows\ndef rows : List Row := Compiler.unoutlineRows {copy} rawRows\n',
         f'theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n',
         '''theorem fourNonzero {F : Type} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
''']
    source,names=_completion_sources(quotients,raw,normalized,copy);out.append(source)
    for name,(left,right) in operands.items():
        source,product_names=_product_completion_sources(
            name,left,right,values[name],certificates[name],raw,normalized,copy)
        out.append(source);names+=product_names
        for suffix,lc in (('left',left),('right',right),('output',values[name])):
            out.append(f'def {name}_{suffix} : Linear := {linear(lc)}\n')
        c=certificates[name]
        a,b=(name+'_right',name+'_left') if c.get('swapped') else (name+'_left',name+'_right')
        if c['kind']=='product':datum='.product '+linear(c['auxiliary'])
        elif c['kind']=='square':datum='.square'
        else:datum=('.foldedLeft ' if c['kind']=='folded_left' else '.foldedRight ')+f'({signed(c["coefficient"])} : Int)'
        out.append(f'''theorem {name}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho {name}_output = eval rho {name}_left * eval rho {name}_right := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product := ScalarRows.checked_product_sound rho one (fourNonzero (F := F)) rows normalized
    {a} {b} {name}_output ({datum}) (by decide)
  simpa only [mul_comm] using product
''')
    for name,point in points.items():
        out.append(f'def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(point[0])},eval rho {linear(point[1])}⟩\n')
    for axis,c in enumerate(quotients):
        out.append(f'def n{axis} : Linear := {linear(c["numerator"])}\ndef d{axis} : Linear := {linear(c["denominator"])}\n')
    out.append('''theorem actual_addition_rows {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    TransferOwnership.AddEquations (coefficientD : F) (ak rho) (contribution rho) (computed rho) := by
''')
    for name in operands:
        out.append(f'  have {name} := {name}_sound rho one satisfied\n')
    out.append('''  change eval rho xx_output = (ak rho).x * (contribution rho).x at xx
  change eval rho yy_output = (ak rho).y * (contribution rho).y at yy
  change eval rho xy_output = eval rho xx_output * eval rho yy_output at xy
''')
    for side,point,role in (('left',points['ak'],'ak'),('right',points['contribution'],'contribution')):
        out.append(f'''  have sum{side} := Compiler.canonical_equal rho sum_{side}
    ({linear(point[0])} ++ {linear(point[1])}) (by decide)
  simp only [eval_append] at sum{side}
  change eval rho sum_{side} = ({role} rho).x + ({role} rho).y at sum{side}
''')
    out.append('''  have sumValue := sum_sound rho one satisfied
  rw [sumleft,sumright] at sumValue
  change eval rho sum_output = ((ak rho).x+(ak rho).y) *
    ((contribution rho).x+(contribution rho).y) at sumValue
''')
    desired={'n0':'(sum_output ++ scaleLinear (-1) xx_output) ++ scaleLinear (-1) yy_output',
             'n1':'yy_output ++ xx_output','d0':'[(0,1)] ++ scaleLinear coefficientD xy_output',
             'd1':'[(0,1)] ++ scaleLinear (-coefficientD) xy_output'}
    targets={'n0':'eval rho sum_output - eval rho xx_output - eval rho yy_output',
             'n1':'eval rho yy_output + eval rho xx_output',
             'd0':'1+(coefficientD : F)*eval rho xy_output','d1':'1-(coefficientD : F)*eval rho xy_output'}
    for name,lc in desired.items():
        out.append(f'''  have {name}Value : eval rho {name} = {targets[name]} := by
    have checked := Compiler.canonical_equal rho {name} ({lc}) (by decide)
    simpa only [eval_append,eval_scale,eval,one,Int.cast_one,Int.cast_neg,one_mul,add_zero,
      sub_eq_add_neg,neg_one_mul,neg_mul] using checked
''')
    for axis in range(2):
        out.append(f'  have q{axis} := {Q}.equation{axis}_sound rho one (fourNonzero (F := F)) satisfied\n')
        out.append(f'  change (computed rho).'+('x' if axis==0 else 'y')+f' * eval rho d{axis} = eval rho n{axis} at q{axis}\n')
        out.append(f'  rw [n{axis}Value,d{axis}Value,xy,xx,yy'+(',sumValue' if axis==0 else '')+f'] at q{axis}\n')
    out.append('''  constructor
  · calc
      (computed rho).x * (1 + Group.delta (coefficientD : F) (ak rho) (contribution rho)) =
          (computed rho).x * (1 + (coefficientD : F) *
            (((ak rho).x * (contribution rho).x) * ((ak rho).y * (contribution rho).y))) := by
              unfold Group.delta
              ring
      _ = ((ak rho).x + (ak rho).y) * ((contribution rho).x + (contribution rho).y) -
          (ak rho).x * (contribution rho).x - (ak rho).y * (contribution rho).y := q0
  · calc
      (computed rho).y * (1 - Group.delta (coefficientD : F) (ak rho) (contribution rho)) =
          (computed rho).y * (1 - (coefficientD : F) *
            (((ak rho).x * (contribution rho).x) * ((ak rho).y * (contribution rho).y))) := by
              unfold Group.delta
              ring
      _ = (ak rho).y * (contribution rho).y + (ak rho).x * (contribution rho).x := q1
theorem actual_add_coordinates {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (actionKey fixedContribution : J)
    (akRole : ak rho = model.coordinates actionKey)
    (contributionRole : contribution rho = model.coordinates fixedContribution)
    (satisfied : Satisfies rho rawRows) :
    computed rho = model.coordinates (actionKey+fixedContribution) := by
  have rows := actual_addition_rows rho one satisfied
  rw [akRole,contributionRole] at rows
  exact TransferOwnership.add_coordinates (coefficientD : F) imaginary model nonSquare imaginarySquare
    actionKey fixedContribution (computed rho) rows.1 rows.2
''')
    exports=['constantLink','fourNonzero',*[name+'_sound' for name in operands],
             'actual_addition_rows','actual_add_coordinates',*names]
    out.extend('#print axioms '+name+'\n' for name in exports)
    out.append('end ShielddSecurity.RuntimeTransferRkAddition\n')
    return _signature_audits(''.join(out))


def completion_plan(data,accepted_roles,extracted):
    """Strict mixed-stage ownership/coverage plan for the actual RK addition.

    This plans constructions only; group-derived denominator legality and
    source/native correspondence remain separate proof obligations. Every
    retained row must occur in the six supported stages or constant link.
    """
    if isinstance(extracted,dict) and extracted.get('algorithm')=='point-add-shared-inverse-v1':
        from . import transfer_rk_point_add
        return transfer_rk_point_add.completion_plan(data,accepted_roles,extracted)
    obj,points,raw,normalized,values,operands,certificates,quotients=_selection(data,accepted_roles,extracted)
    computed={source_index(ref['source']) for ref in obj['spend']['computed']}
    kept={0,obj['constant_copy']}
    # All observed caller, scalar, contribution and externally supplied RK
    # columns are owned elsewhere. Only the computed-point handles may change.
    for handle,lc in accepted_roles['observed'].items():
        if handle not in computed:kept.update(c for c,_ in lc)
    def keep_refs(value):
        if isinstance(value,list):
            for ref in value:keep_refs(ref)
        elif isinstance(value,dict):
            if set(value)=={'source'}:
                kept.update(c for c,_ in accepted_roles['observed'][source_index(value['source'])])
            else:
                for ref in value.values():keep_refs(ref)
    keep_refs(obj['caller']);keep_refs(obj['rnk_bindings'])
    stages=[]
    for name in ('xx','yy','sum','xy'):
        c=arithmetic.product_completion_certificate(*operands[name],values[name],certificates[name],normalized)
        if c is None:raise relation.RelationError('RK completion unsupported product shape: '+name)
        stages.append(dict(kind='product',role=name,**c))
    for axis,c in enumerate(quotients):
        completed=arithmetic.completion_certificate(c,normalized)
        if completed is None:raise relation.RelationError('RK completion unsupported quotient shape: '+str(axis))
        stages.append(dict(kind='quotient',role='quotient'+str(axis),**completed))
    prior=set();owned=set();covered=set()
    for stage in stages:
        writes={stage['auxiliary'],stage['output']} if stage['kind']=='product' else {
            stage['quotient'],stage['product'],stage['auxiliary']}
        if writes & (kept|owned|prior):
            raise relation.RelationError('RK completion writes alias kept/prior support: '+stage['role'])
        if covered & set(stage['rows']):raise relation.RelationError('RK completion original row ownership overlaps')
        owned.update(writes);covered.update(stage['rows'])
        for index in stage['rows']:
            for side in normalized[index]:prior.update(c for c,_ in side)
    constant=next(i for i,row in raw.items() if row==(canonical([(0,1),(obj['constant_copy'],-1)]),()))
    if covered|{constant}!=set(raw):raise relation.RelationError('RK completion does not cover every selected original row')
    return dict(stages=stages,kept=sorted(kept),writes=sorted(owned),constant_row=constant,
                original_rows=sorted(raw),scope='exact local mixed-stage plan; denominator/source/native/caller completion proofs pending')


def generate_completion(data,accepted_roles,extracted):
    """Emit exact mixed construction; legal denominators are explicit inputs.

    This is a diagnostic local completion candidate. Its legality inputs must
    be derived from the standard curve and preceding computed products before
    it can contribute to a caller or full Transfer completeness theorem.
    """
    if isinstance(extracted,dict) and extracted.get('algorithm')=='point-add-shared-inverse-v1':
        from . import transfer_rk_point_add
        return transfer_rk_point_add.generate_completion(data,accepted_roles,extracted)
    plan=completion_plan(data,accepted_roles,extracted)
    obj,points,raw,_,values,operands,certificates,_=_selection(data,accepted_roles,extracted)
    copy=obj['constant_copy'];steps=[];expected={};definitions=[]
    for i,stage in enumerate(plan['stages']):
        if stage['kind']=='product':
            left,right,remainder=(linear(stage[key]) for key in ('left','right','remainder'))
            output,auxiliary=stage['output'],stage['auxiliary']
            steps.append(f'.compiler (.product {left} {right} {remainder} {output} {auxiliary})')
            rows=[f'⟨Compiler.subtract {left} {right},[({auxiliary},1)]⟩',
                  f'⟨{left} ++ {right},[({auxiliary},1)] ++ scaleLinear 4 ([({output},1)] ++ {remainder})⟩']
        else:
            n,d,r=(linear(stage[key]) for key in ('numerator','denominator','remainder'))
            q,p,a=(stage[key] for key in ('quotient','product','auxiliary'))
            definitions += [f'def numerator{i-4} : Linear := {n}\n',f'def denominator{i-4} : Linear := {d}\n',
                            f'def remainder{i-4} : Linear := {r}\n']
            steps.append(f'.quotient numerator{i-4} denominator{i-4} remainder{i-4} {q} {p} {a}')
            rows=[f'⟨Compiler.subtract [({q},1)] {d},[({a},1)]⟩',
                  f'⟨[({q},1)] ++ {d},[({a},1)] ++ scaleLinear 4 ([({p},1)] ++ {r})⟩',
                  f'⟨Compiler.subtract ([({p},1)] ++ {r}) {n},[]⟩']
        expected.update(zip(stage['rows'],rows))
    expected[plan['constant_row']]='⟨[],[]⟩'
    products='['+',\n  '.join(steps[:4])+']'
    q0,q1=plan['stages'][4:]
    extend=lambda rho,axis,c:f'GroupRowCompletion.extendQuotient ({rho}) numerator{axis} denominator{axis} remainder{axis} {c["quotient"]} {c["product"]} {c["auxiliary"]}'
    out=['''import ShielddSecurity.GroupCircuitOrder
import ShielddSecurity.ScalarRows
namespace ShielddSecurity.RuntimeTransferRkAdditionCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
''',f'-- Exact local relation: {obj["relation_digest"]}; metadata SHA256: {hashlib.sha256(data).hexdigest()}\n',
         '-- Denominator/source/native and full Transfer joins remain explicit obligations.\n',
         f'def modulus : Nat := {relation.MODULUS}\ndef kept : List Nat := {plan["kept"]}\n',
         f'def completionWrites : List Nat := {plan["writes"]}\ndef originalRows : List Nat := {sorted(raw)}\n',
         'def rawRows : List Row := ['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(raw))+']\n',
         *definitions,f'def productStages : List GroupCircuitCompletion.Step := {products}\n',
         'def completionSteps : List GroupCircuitCompletion.Step := productStages ++ ['+','.join(steps[4:])+',.compiler (.equal [] [])]\n',
         '''def productAssignment {F : Type} [Field F] (rho : Nat → F) :=
  GroupCircuitCompletion.run rho productStages
''',f'def afterX {{F : Type}} [Field F] (rho : Nat → F) := {extend("productAssignment rho",0,q0)}\n',
         f'def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) := {extend("afterX rho",1,q1)}\n',
         '''theorem completion_run {F : Type} [Field F] (rho : Nat → F) :
    GroupCircuitCompletion.run rho completionSteps = completeAssignment rho := rfl
theorem completion_ordered : GroupCircuitCompletion.Topological kept [] completionSteps :=
  GroupCircuitOrder.checked_order kept [] completionSteps (by decide)
theorem denominator_after_x {F : Type} [Field F] (rho : Nat → F) :
    eval (afterX rho) denominator1 = eval (productAssignment rho) denominator1 := by
''',f'  exact GroupRowCompletion.eval_preserves (productAssignment rho) numerator0 denominator0 remainder0 denominator1 {q0["quotient"]} {q0["product"]} {q0["auxiliary"]} (by simp [denominator1,GroupRowCompletion.writes])\n',
         '''theorem completion_legal {F : Type} [Field F] (rho : Nat → F)
    (legalX : eval (productAssignment rho) denominator0 ≠ 0)
    (legalY : eval (productAssignment rho) denominator1 ≠ 0) :
    GroupCircuitCompletion.Legal rho completionSteps := by
  change True ∧ True ∧ True ∧ True ∧
    (eval (productAssignment rho) denominator0 ≠ 0) ∧
    (eval (afterX rho) denominator1 ≠ 0) ∧
    (eval (completeAssignment rho) [] = eval (completeAssignment rho) []) ∧ True
  refine ⟨True.intro,True.intro,True.intro,True.intro,legalX,?_,rfl,True.intro⟩
  rw [denominator_after_x]
  exact legalY
theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈
    GroupCircuitCompletion.emitted completionSteps,
''',f'''    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in raw)+'\n']
    for index in sorted(raw):
        out.append(f'''  · refine ⟨{expected[index]}, ?_, by decide, by decide⟩
    simp [completionSteps,productStages,GroupCircuitCompletion.emitted,GroupCircuitCompletion.Step.rows,
      CompilerCompletion.Step.rows,ScalarCompletion.productRows,GroupRowCompletion.quotientRows,
      numerator0,denominator0,remainder0,numerator1,denominator1,remainder1,Compiler.subtract,scaleLinear]
''')
    out.append(f'''theorem actual_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (linked : rho {copy} = rho 0)
    (legalX : eval (productAssignment rho) denominator0 ≠ 0)
    (legalY : eval (productAssignment rho) denominator1 ≠ 0) :
    Satisfies (completeAssignment rho) rawRows ∧
      (∀ column ∈ kept, completeAssignment rho column = rho column) := by
  rw [← completion_run]
  exact GroupCircuitCompletion.original_rows_complete rho completionSteps kept rawRows {copy}
    completion_ordered (completion_legal rho legalX legalY) (by decide) (by decide) linked original_coverage
''')
    # Discharge division legality from products that were just constructed,
    # independently valid input points, and the complete-curve field facts.
    out.append(f'def coefficientD : Int := {signed(D)}\n')
    for name,point in (('actionKey',points['ak']),('fixedContribution',points['contribution'])):
        out.append(f'def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(point[0])},eval rho {linear(point[1])}⟩\n')
    out.append('''theorem product_kept {F : Type} [Field F] (rho : Nat → F) (column : Nat)
    (member : column ∈ kept) : productAssignment rho column = rho column :=
  GroupCircuitCompletion.run_preserves rho productStages kept []
    (GroupCircuitOrder.checked_order kept [] productStages (by decide)) column member
theorem product_eval_kept {F : Type} [Field F] (rho : Nat → F) (terms : Linear)
    (included : ∀ term ∈ terms, term.1 ∈ kept) :
    eval (productAssignment rho) terms = eval rho terms := by
  apply eval_agrees
  intro term member
  exact product_kept rho term.1 (included term member)
theorem product_inputs_preserved {F : Type} [Field F] (rho : Nat → F) :
    actionKey (productAssignment rho) = actionKey rho ∧
      fixedContribution (productAssignment rho) = fixedContribution rho := by
  constructor
''')
    for name,point in (('actionKey',points['ak']),('fixedContribution',points['contribution'])):
        out.append(f'  · apply congrArg₂ Group.Point.mk\n')
        for axis in range(2):
            out.append(f'    · exact product_eval_kept rho {linear(point[axis])} (by simp [kept])\n')
    out.append('''theorem constructed_denominators {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) :
    eval (productAssignment rho) denominator0 = 1 + Group.delta (coefficientD : F)
      (actionKey rho) (fixedContribution rho) ∧
    eval (productAssignment rho) denominator1 = 1 - Group.delta (coefficientD : F)
      (actionKey rho) (fixedContribution rho) := by
  let built := productAssignment rho
  have oneBuilt : built 0 = 1 := (product_kept rho 0 (by decide)).trans one
  have productRows := GroupCircuitCompletion.run_constructs rho productStages kept
    (GroupCircuitOrder.checked_order kept [] productStages (by decide))
    (by exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro⟩)
''')
    for name,stage in zip(('xx','yy','sum','xy'),plan['stages'][:4]):
        left,right=stage['left'],stage['right']
        out.append(f'''  have {name} := ScalarRows.checked_product_sound built oneBuilt four
    (GroupCircuitCompletion.emitted productStages) productRows
    {linear(left)} {linear(right)} {linear(values[name])}
    (.product [({stage['auxiliary']},1)]) (by decide)
''')
    out.append('  have xyValue : eval built '+linear(values['xy'])+' =\n'+
               '    (actionKey built).x * (fixedContribution built).x *\n'+
               '      (actionKey built).y * (fixedContribution built).y := by\n')
    for name,axis in (('xx','x'),('yy','y')):
        out.append(f'''    have {name}Value : eval built {linear(values[name])} = (actionKey built).{axis} * (fixedContribution built).{axis} := by
      simpa only [actionKey,fixedContribution,mul_comm] using {name}
''')
    out.append(f'''    have joined : eval built {linear(values['xy'])} = eval built {linear(values['xx'])} * eval built {linear(values['yy'])} := by
      simpa only [mul_comm] using xy
    rw [xxValue,yyValue] at joined
    exact joined.trans (by ring)
  have inputs := product_inputs_preserved rho
  have oneLinear : eval built [(0,1)] = 1 := by
    simp only [eval,oneBuilt,Int.cast_one,one_mul,add_zero]
  constructor
''')
    for axis,sign in ((0,1),(1,-1)):
        expected='[(0,1)] ++ scaleLinear '+('coefficientD' if sign==1 else '(-coefficientD)')+' '+linear(values['xy'])
        out.append(f'''  · have checked := Compiler.canonical_equal built denominator{axis} ({expected}) (by decide)
    simp only [eval_append,eval_scale,oneLinear,Int.cast_neg] at checked
    rw [checked,xyValue]
    change _ = 1 {'+' if sign==1 else '-'} Group.delta (coefficientD : F) (actionKey rho) (fixedContribution rho)
    rw [← inputs.1,← inputs.2]
    unfold Group.delta
    ring
''')
    out.append('''theorem actual_curve_rows_complete {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
'''+f'    (linked : rho {copy} = rho 0)\n'+'''    (keyValid : Group.OnCurve (coefficientD : F) (actionKey rho))
    (contributionValid : Group.OnCurve (coefficientD : F) (fixedContribution rho)) :
    Satisfies (completeAssignment rho) rawRows ∧
      (∀ column ∈ kept, completeAssignment rho column = rho column) := by
  have formulas := constructed_denominators rho one four
  have nonzero := Group.denominators_nonzero (coefficientD : F) imaginary nonSquare imaginarySquare
    (actionKey rho) (fixedContribution rho) keyValid contributionValid
  apply actual_rows_complete rho linked
  · rw [formulas.1]
    exact nonzero.1
  · rw [formulas.2]
    exact nonzero.2
''')
    out.extend('#print axioms '+name+'\n' for name in ('completion_run','completion_ordered','denominator_after_x',
               'completion_legal','original_coverage','actual_rows_complete','product_kept','product_eval_kept',
               'product_inputs_preserved','constructed_denominators','actual_curve_rows_complete'))
    out.append('end ShielddSecurity.RuntimeTransferRkAdditionCompletion\n')
    return _signature_audits(''.join(out))


def generate_whole_completion(data,accepted_roles,extracted):
    """Construct actual addition rows and derive curve/group output semantics.

    Public RK equality rows still require the independent legal public-view
    source join; they are not asserted from the computed-point construction.
    """
    obj,points,*_=_selection(data,accepted_roles,extracted)
    copy=obj['constant_copy'];M='ShielddSecurity.RuntimeTransferRkAddition'
    namespace='ShielddSecurity.RuntimeTransferRkAdditionCompletion'
    source=generate_completion(data,accepted_roles,extracted).removesuffix('end '+namespace+'\n')
    source='import '+M+'\n'+source
    source+='''private theorem eval_kept {F : Type} [Field F] (rho built : Nat → F) (terms : Linear)
    (preserves : ∀ column ∈ kept, built column = rho column)
    (checked : terms.all (fun term => decide (term.1 ∈ kept)) = true) : eval built terms = eval rho terms := by
  apply eval_agrees
  intro term member
  exact preserves term.1 (of_decide_eq_true (List.all_eq_true.mp checked term member))
'''
    source+=f'''theorem actual_addition_complete {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary * imaginary = -1)
    (linked : rho {copy} = rho 0) (keyValid : Group.OnCurve (coefficientD : F) (actionKey rho))
    (contributionValid : Group.OnCurve (coefficientD : F) (fixedContribution rho)) :
    Satisfies (completeAssignment rho) {M}.rawRows ∧
      Group.OnCurve (coefficientD : F) ({M}.computed (completeAssignment rho)) ∧
      (∀ column ∈ kept, completeAssignment rho column = rho column) := by
  have completed := actual_curve_rows_complete rho one four imaginary nonSquare imaginarySquare
    linked keyValid contributionValid
  let built := completeAssignment rho
  have oneBuilt : built 0 = 1 := (completed.2 0 (by decide)).trans one
  have allRows : Satisfies built {M}.rawRows := completed.1
'''
    for name,target in (('keySame','ak'),('contributionSame','contribution')):
        local='actionKey' if target=='ak' else 'fixedContribution'
        source+=f'  have {name} : {M}.{target} built = {local} rho := by\n    apply congrArg₂ Group.Point.mk\n'
        for lc in points[target]:source+=f'    · exact eval_kept rho built {linear(lc)} completed.2 (by decide)\n'
    source+=f'''  have equations := {M}.actual_addition_rows built oneBuilt allRows
  have xRow : ({M}.computed built).x *
      (1 + Group.delta (coefficientD : F) ({M}.ak built) ({M}.contribution built)) =
        Group.cross ({M}.ak built) ({M}.contribution built) :=
    equations.1.trans (by unfold Group.cross; ring)
  have outputValid := Group.affine_rows_onCurve (coefficientD : F) imaginary nonSquare imaginarySquare
    ({M}.ak built) ({M}.contribution built) ({M}.computed built)
    (by rw [keySame]; exact keyValid) (by rw [contributionSame]; exact contributionValid)
    xRow equations.2
  exact ⟨allRows,outputValid,completed.2⟩
#print axioms actual_addition_complete
theorem actual_addition_group_complete {{F J : Type}} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary * imaginary = -1)
    (linked : rho {copy} = rho 0) (key contribution : J)
    (keyRole : actionKey rho = model.coordinates key)
    (contributionRole : fixedContribution rho = model.coordinates contribution) :
    {M}.computed (completeAssignment rho) = model.coordinates (key + contribution) := by
  have keyValid : Group.OnCurve (coefficientD : F) (actionKey rho) := by
    rw [keyRole]
    exact model.onCurve key
  have contributionValid : Group.OnCurve (coefficientD : F) (fixedContribution rho) := by
    rw [contributionRole]
    exact model.onCurve contribution
  have completed := actual_addition_complete rho one four imaginary nonSquare imaginarySquare
    linked keyValid contributionValid
  let built := completeAssignment rho
  have oneBuilt : built 0 = 1 := (completed.2.2 0 (by decide)).trans one
'''
    for name,target,local,role in (('keyBuilt','ak','actionKey','keyRole'),
                                   ('contributionBuilt','contribution','fixedContribution','contributionRole')):
        source+=f'  have {name} : {M}.{target} built = model.coordinates '+('key' if target=='ak' else 'contribution')+' := by\n'
        source+=f'    have same : {M}.{target} built = {local} rho := by\n      apply congrArg₂ Group.Point.mk\n'
        for lc in points[target]:source+=f'      · exact eval_kept rho built {linear(lc)} completed.2.2 (by decide)\n'
        source+=f'    exact same.trans {role}\n'
    source+=f'''  exact {M}.actual_add_coordinates built oneBuilt imaginary model nonSquare imaginarySquare
    key contribution keyBuilt contributionBuilt completed.1
#print axioms actual_addition_group_complete
end {namespace}
'''
    return _signature_audits(source)


def generate_spend_join(data,accepted_roles,extracted,caller_source=None):
    """Join actual caller/AK, canonical fixed rows, addition and RK on one rho."""
    _selection(data,accepted_roles,extracted)
    source='''import ShielddSecurity.RuntimeTransferAuthorizationCaller
import ShielddSecurity.RuntimeTransferFixedSpend
import ShielddSecurity.RuntimeTransferRkAddition
import ShielddSecurity.RuntimeTransferRkBinding
namespace ShielddSecurity.RuntimeTransferSpendAuthorization
set_option maxHeartbeats 500000
def modulus : Nat := RuntimeTransferFixedSpend.modulus
def coefficientD : Int := RuntimeTransferFixedSpend.coefficientD
def blocks : List (List Row) := [RuntimeTransferAuthorizationCaller.rawRows,
  RuntimeTransferFixedSpend.rawRows,RuntimeTransferRkAddition.rawRows,RuntimeTransferRkBinding.rawRows]
def rawRows : List Row := blocks.flatten
theorem caller_projection {F : Type} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho rawRows) : Satisfies rho RuntimeTransferAuthorizationCaller.rawRows := by
  intro row member
  exact satisfied row (List.mem_flatten.mpr ⟨RuntimeTransferAuthorizationCaller.rawRows,by simp [blocks],member⟩)
theorem ak_role {F : Type} [Field F] (rho : Nat → F) :
    RuntimeTransferRkAddition.ak rho = RuntimeTransferAuthorizationCaller.akPoint rho := rfl
theorem contribution_role {F : Type} [Field F] (rho : Nat → F) :
    RuntimeTransferRkAddition.contribution rho = RuntimeTransferFixedSpend.contribution rho := rfl
theorem computed_role {F : Type} [Field F] (rho : Nat → F) :
    RuntimeTransferRkAddition.computed rho = RuntimeTransferRkBinding.computed rho := rfl
theorem actual_spend_rk {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (standardGenerator : J)
    (generatorRole : (RuntimeTransferFixedSpend.generator : Group.Point F) = model.coordinates standardGenerator)
    (satisfied : Satisfies rho rawRows) :
    ∃ actionKey : J,
      model.coordinates actionKey = RuntimeTransferAuthorizationCaller.akPoint rho ∧
      RuntimeTransferAk.subgroupOrder • actionKey = 0 ∧ actionKey ≠ 0 ∧
      binary (RuntimeTransferFixedSpend.decodedBits rho) < Scalar.order ∧
      (binary (RuntimeTransferFixedSpend.decodedBits rho) : F) = eval rho RuntimeTransferRandomizer.privateValue ∧
      RuntimeTransferRkBinding.rk rho = model.coordinates
        (actionKey + binary (RuntimeTransferFixedSpend.decodedBits rho) • standardGenerator) := by
  have callerSat := caller_projection rho satisfied
  have akSat : Satisfies rho RuntimeTransferAk.rawRows := by
    intro row member
    exact callerSat row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
      (List.mem_append.mpr (Or.inl member))))))
  have fixedSat : Satisfies rho RuntimeTransferFixedSpend.rawRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨RuntimeTransferFixedSpend.rawRows,by simp [blocks],member⟩)
  have additionSat : Satisfies rho RuntimeTransferRkAddition.rawRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨RuntimeTransferRkAddition.rawRows,by simp [blocks],member⟩)
  have bindingSat : Satisfies rho RuntimeTransferRkBinding.rawRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨RuntimeTransferRkBinding.rawRows,by simp [blocks],member⟩)
  obtain ⟨actionKey,keyRole,keySubgroup,keyNonzero⟩ := RuntimeTransferAk.actual_ak_subgroup
    model standardOrder rho one akSat
  rw [← RuntimeTransferAuthorizationCaller.akPoint_role rho] at keyRole
  have fixed := RuntimeTransferFixedSpend.actual_fixed_canonical rho one four imaginary model nonSquare
    imaginarySquare standardGenerator generatorRole fixedSat
  have output := RuntimeTransferRkAddition.actual_add_coordinates rho one imaginary model nonSquare
    imaginarySquare actionKey (binary (RuntimeTransferFixedSpend.decodedBits rho) • standardGenerator)
    ((ak_role rho).trans keyRole.symm) ((contribution_role rho).trans fixed.2.2) additionSat
  have bound := RuntimeTransferRkBinding.actual_rk_binding rho bindingSat
  have joined := ((computed_role rho).trans bound).symm.trans output
  exact ⟨actionKey,keyRole,keySubgroup,keyNonzero,fixed.1,fixed.2.1,joined⟩
#print axioms caller_projection
#print axioms ak_role
#print axioms contribution_role
#print axioms computed_role
#print axioms actual_spend_rk
end ShielddSecurity.RuntimeTransferSpendAuthorization
'''
    if caller_source is not None:
        # Reuse the maintained caller's exact final signature, so adding spend
        # rows preserves all its owner/DH/ring/hash conclusions on this rho.
        # Its proof remains delegated to that separately generated module.
        if not isinstance(caller_source,str):
            raise relation.RelationError('maintained caller theorem signature required')
        start=caller_source.find('theorem actual_caller {')
        ending=caller_source.find(' := by\n',start)
        if (start<0 or ending<start or
                'namespace ShielddSecurity.RuntimeTransferAuthorizationCaller\n' not in caller_source):
            raise relation.RelationError('maintained caller theorem signature required')
        signature=caller_source[start:ending]
        required='(satisfied : Satisfies rho rawRows)'
        if signature.count(required)!=1:
            raise relation.RelationError('maintained caller satisfied-row signature changed')
        signature=signature.replace('theorem actual_caller {','theorem actual_caller_with_spend_rows {',1)
        signature=signature.replace(required,'(satisfied : Satisfies rho RuntimeTransferSpendAuthorization.rawRows)')
        source+='namespace ShielddSecurity.RuntimeTransferAuthorizationCaller\n'+signature+''' := by
  exact actual_caller rho one four codec model standardOrder
    (RuntimeTransferSpendAuthorization.caller_projection rho satisfied)
#print axioms actual_caller_with_spend_rows
end ShielddSecurity.RuntimeTransferAuthorizationCaller
'''
    return _signature_audits(source)
