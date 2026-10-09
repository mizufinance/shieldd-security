"""Fresh RK subgroup construction candidates; never qualification or evidence.

The observer/extractor supplies exact original rows. This module reconstructs
their materializations from those rows, and reuses the maintained independent
Edwards cone generator. Native witness/assertion transport is separate from
the unconditional materialization constructor, not a satisfaction premise.
"""
import hashlib
import re
from . import transfer_rk_subgroup as rk, transfer_arithmetic as arithmetic
from .generate_hash_round import linear
from .generate_group_cones import generate_checked


def completion_plan(data, accepted_roles, extracted):
    state = rk.inspect_metadata(data, accepted_roles)
    obj = state['metadata']
    raw, normalized = arithmetic.normalize_selection(extracted, obj, hashlib.sha256(data).hexdigest())
    records = extracted.get('allocation')
    if not isinstance(records, dict) or set(records) != {'witnesses', 'stages', 'nonlinear_writes'}:
        raise rk.relation.RelationError('RK subgroup completion allocation schema')
    for key in ('witnesses','nonlinear_writes'):
        values=records[key]
        if not isinstance(values,list) or any(type(c) is not int or not 0 <= c < obj['domain_size'] for c in values):
            raise rk.relation.RelationError('RK subgroup completion allocation columns')
    witnesses = sorted(3+i for _, i in state['inputs'][2:4] + state['nonidentity'][1:] +
                       tuple(state['formulas']['inverse_witnesses']))
    kept = {0, obj['constant_copy'], *witnesses}
    kept.update(c for terms in accepted_roles['observed'].values() for c, _ in terms)
    stages, owned, prior, covered = [], set(), set(), set()
    allocations = []
    for source, (multiply, left, right) in state['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0:
            continue
        a, b, z = (state['derived'][h] for h in (left, right, source))
        certificate = arithmetic.product_certificate(a, b, z, normalized)
        if left == right:
            pivots = [c for c, value in z if value == 1 and c not in {c for c, _ in a}]
            if len(pivots) != 1 or certificate['kind'] != 'square':
                raise rk.relation.RelationError('RK subgroup completion square pivot')
            output = pivots[0]
            stage = dict(kind='square', input=a, remainder=tuple((c,v) for c,v in z if c != output),
                         output=output, rows=certificate['rows'])
            writes = {output}
        else:
            stage = arithmetic.product_completion_certificate(a, b, z, certificate, normalized)
            if stage is None:
                raise rk.relation.RelationError('RK subgroup completion product pivot')
            stage = dict(kind='product', **stage)
            writes = {stage['output'], stage['auxiliary']}
        support = {c for key in ('input','left','right','remainder') for c,_ in stage.get(key,())}
        if writes & (kept | owned | prior | support) or covered & set(stage['rows']):
            raise rk.relation.RelationError('RK subgroup completion ownership/order overlap')
        owned.update(writes); covered.update(stage['rows'])
        prior.update(c for index in stage['rows'] for side in normalized[index] for c,_ in side)
        allocations.append(dict(source=list(source),rows=stage['rows'],writes=sorted(writes),kind=certificate['kind']))
        stages.append(stage)
    # Allocation is retained for replay, but must agree with fresh row-derived
    # certificates after JSON roundtrips; it cannot authorize a new pivot.
    supplied = records['stages']
    if not isinstance(supplied,list) or len(supplied) != len(allocations):
        raise rk.relation.RelationError('RK subgroup completion allocation length')
    for actual, expected in zip(supplied, allocations):
        if not isinstance(actual,dict) or set(actual) != set(expected) or any(
                actual[k] != expected[k] for k in ('source','rows','kind')) or not isinstance(actual['writes'],list) or any(
                type(c) is not int for c in actual['writes']) or sorted(actual['writes']) != expected['writes']:
            raise rk.relation.RelationError('RK subgroup completion allocation mismatch')
    if records['witnesses'] != witnesses or records['nonlinear_writes'] != sorted(owned):
        raise rk.relation.RelationError('RK subgroup completion witness/write mismatch')
    roles = {};templates=extracted.get('templates')
    if not isinstance(templates,list) or len(templates)>2048:
        raise rk.relation.RelationError('RK subgroup completion template collection')
    for template in templates:
        if (not isinstance(template,dict) or set(template) != {'roles','row'} or
                not isinstance(template['roles'],list) or not template['roles'] or
                any(not isinstance(r,str) for r in template['roles']) or
                type(template['row']) is not int or template['row'] not in raw):
            raise rk.relation.RelationError('RK subgroup completion template framing')
        for role in template['roles']:
            if role in roles: raise rk.relation.RelationError('RK subgroup completion duplicate assertion role')
            roles[role] = template['row']
    assertions = ['curve','rk-link.0','rk-link.1'] + ['inverse-assert.'+str(i) for i in range(4)]
    expected_roles = {'constant-copy', *assertions} | {
        'node.'+str(h[1])+'.square' for h,(m,l,r) in state['nodes'].items()
        if m and l == r and l[0] != 0}
    if set(roles) != expected_roles or covered | {roles[x] for x in assertions+['constant-copy']} != set(raw):
        raise rk.relation.RelationError('RK subgroup completion exact original coverage')
    constant = roles['constant-copy']
    if raw[constant] != (rk.canonical([(0,1),(obj['constant_copy'],-1)]),()):
        raise rk.relation.RelationError('RK subgroup completion constant link')
    expected_assertions = [(rk.combine(state['derived'][state['curve'][0]],state['derived'][state['curve'][1]],-1),())]
    expected_assertions += [(rk.combine(state['derived'][state['inputs'][i]],state['derived'][state['doubles'][-1][i+2]],-1),()) for i in range(2)]
    expected_assertions += [(rk.combine(state['derived'][h],[(0,1)],-1),())
                           for h in state['formulas']['inverse_assert_products']+[state['nonidentity_product']]]
    for role, expected in zip(assertions,expected_assertions):
        a,b=normalized[roles[role]]
        if b != expected[1] or a not in (expected[0],rk.canonical((c,-v) for c,v in expected[0])):
            raise rk.relation.RelationError('RK subgroup completion changed assertion')
    return dict(state=state,raw=raw,normalized=normalized,stages=stages,kept=sorted(kept),
                writes=sorted(owned),constant_row=constant,roles=roles,assertions=assertions,
                materialization_rows=sorted(covered|{constant}))


def _audits(source, names):
    return source + ''.join('set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n' for name in names)


def generate_materialization(data, accepted_roles, extracted):
    """Construct actual nonlinear rows without a legal-row/output premise.

    All eight source witness columns are preserved here. The subsequent native
    witness assignment sets the six private columns before this constructor.
    Seven arithmetic assertions are deliberately not assumed or included in
    this module's completion conclusion.
    """
    plan=completion_plan(data,accepted_roles,extracted); obj=plan['state']['metadata']; copy=obj['constant_copy']
    steps=[]; expected={};emitted=[]
    for stage in plan['stages']:
        if stage['kind']=='square':
            a,r=linear(stage['input']),linear(stage['remainder']); o=stage['output']
            steps.append(f'.compiler (.square {a} {r} {o})')
            rows=[f'⟨{a},[({o},1)] ++ {r}⟩']
        else:
            a,b,r=(linear(stage[key]) for key in ('left','right','remainder'));o,u=stage['output'],stage['auxiliary']
            steps.append(f'.compiler (.product {a} {b} {r} {o} {u})')
            rows=[f'⟨Compiler.subtract {a} {b},[({u},1)]⟩',
                  f'⟨{a} ++ {b},[({u},1)] ++ scaleLinear 4 ([({o},1)] ++ {r})⟩']
        expected.update(zip(stage['rows'],rows))
        emitted+=rows
    steps.append('.compiler (.equal [] [])');expected[plan['constant_row']]='⟨[],[]⟩'
    emitted.append('⟨[],[]⟩')
    indices=plan['materialization_rows'];raw=plan['raw']
    out=['''import ShielddSecurity.GroupCircuitOrder
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferRkSubgroupMaterialization
''',f'-- Metadata SHA256: {hashlib.sha256(data).hexdigest()}; relation: {obj["relation_digest"]}\n',
         '-- Actual bounded materializations only; no qualification or whole Transfer conclusion.\n',
         f'def modulus : Nat := {rk.P}\ndef kept : List Nat := {plan["kept"]}\n',
         f'def originalIndices : List Nat := {indices}\n',
         'def rawRows : List Row := ['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in indices)+']\n',
         'def steps : List GroupCircuitCompletion.Step := ['+',\n'.join(steps)+']\n',
         'def expectedRows : List Row := ['+',\n'.join(emitted)+']\n',
         'private theorem emitted_exact : GroupCircuitCompletion.emitted steps = expectedRows := rfl\n',
         '''def assignment {F : Type} [Field F] (base : Nat → F) := GroupCircuitCompletion.run base steps
theorem ordered : GroupCircuitCompletion.Topological kept [] steps :=
  GroupCircuitOrder.checked_order kept [] steps (by decide)
theorem legal {F : Type} [Field F] (base : Nat → F) : GroupCircuitCompletion.Legal base steps := by
''', '  change '+' ∧ '.join(['True']*(len(steps)-1)+['((0 : F) = 0)','True'])+'\n  simp\n',
         '''theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈ GroupCircuitCompletion.emitted steps,
''',f'''    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  rw [emitted_exact]
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in indices)+'\n']
    for index in indices:
        out.append(f'  · exact ⟨{expected[index]}, by decide, by decide, by decide⟩\n')
    out.append(f'''theorem materialized_complete {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (linked : base {copy} = base 0) :
    Satisfies (assignment base) rawRows ∧ (∀ column ∈ kept, assignment base column = base column) :=
  GroupCircuitCompletion.original_rows_complete base steps kept rawRows {copy}
    ordered (legal base) (by decide) (by decide) linked original_coverage
theorem eval_kept {{F : Type}} [Field F] (base : Nat → F) (terms : Linear)
    (included : ∀ term ∈ terms, term.1 ∈ kept) : eval (assignment base) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact GroupCircuitCompletion.run_preserves base steps kept [] ordered term.1 (included term member)
''')
    out.append(_audits('',('ordered','legal','original_coverage','materialized_complete','eval_kept')))
    out.append('end ShielddSecurity.RuntimeTransferRkSubgroupMaterialization\n')
    return ''.join(out)


def cone_selection(data, accepted_roles, extracted):
    """Exact row adapter for the existing Edwards cone generator.

    Only materializations and the constant link are included. The cone proofs
    can therefore be applied to the constructor conclusion before any native
    assertion is discharged, avoiding circular row-satisfaction assumptions.
    """
    plan=completion_plan(data,accepted_roles,extracted);state=plan['state'];derived=state['derived']
    name=lambda handle:'cwn'[handle[0]]+str(handle[1])
    stages={tuple(record['source']):stage for record,stage in zip(extracted['allocation']['stages'],plan['stages'])}
    cones=[]
    for index,matched in enumerate(state['formulas']['cones']):
        role=matched['formula'] if index<2 else 'double'+str((index-2)//3)+'.'+('after.' if matched['formula'] in ('x','y') else '')+matched['formula']
        inputs=[name(h) for h in matched['inputs']];source=matched['source'];output=name(matched['output'])
        ordered=[];visited=set()
        def visit(identity):
            if identity in visited:return
            visited.add(identity);node=source[identity]
            if identity not in inputs and node['kind'] in ('add','mul'):
                visit(node['left']);visit(node['right'])
            ordered.append(identity)
        visit(output)
        if visited != {identity for _,identity in matched['pairs']}:
            raise rk.relation.RelationError('RK subgroup cone exact source closure')
        certificates={}
        for identity in ordered:
            node=source[identity]
            if identity in inputs:certificate=dict(kind='input')
            elif node['kind']=='constant':certificate=dict(kind='constant',coefficient=node['value'])
            elif node['kind']=='add':certificate=dict(kind='add')
            else:
                left,right=(derived[('cwn'.index(source[identity][side][0]),int(source[identity][side][1:]))] for side in ('left','right'))
                constants=[(side,terms[0][1] if terms else 0) for side,terms in (('left',left),('right',right)) if all(c==0 for c,_ in terms)]
                if constants:
                    side,coefficient=constants[0];certificate=dict(kind='folded_'+side,coefficient=coefficient)
                else:
                    stage=stages[(2,int(identity[1:]))]
                    if stage['kind']=='square':certificate=dict(kind='square',rows=stage['rows'])
                    else:
                        original=arithmetic.product_certificate(left,right,derived[(2,int(identity[1:]))],plan['normalized'])
                        certificate=dict(kind='product',rows=stage['rows'],auxiliary=((stage['auxiliary'],1),),
                                         swapped=original.get('swapped',False))
            certificates[identity]=certificate
        cones.append(dict(role=role,source=source,inputs=inputs,output=output,ordered=ordered,certificates=certificates))
    return dict(outline=state['metadata']['constant_copy'],rows={i:plan['raw'][i] for i in plan['materialization_rows']},
                observations={name(h):('linear',lc) for h,lc in derived.items()},cones=cones)


def generate_cones(data, accepted_roles, extracted):
    selected=cone_selection(data,accepted_roles,extracted)
    source=generate_checked(selected,hashlib.sha256(data).hexdigest(),extracted['identity']['relation_digest'],
                            'RuntimeTransferRkSubgroupCones',True)
    # The maintained cone generator expects the source's operand order. An
    # actual compiler may orient the first square oppositely. Keep the exact
    # source graph unchanged, and transport the checked product by commutation.
    for cone in selected['cones']:
        prefix=cone['role'].replace('.','_')
        for identity,certificate in cone['certificates'].items():
            if not certificate.get('swapped'):continue
            node=cone['source'][identity]
            left,right=(prefix+'_'+node[side] for side in ('left','right'))
            output=prefix+'_'+identity;aux=linear(certificate['auxiliary'])
            original=f'''    exact Compiler.checked_product_sound rho rows {left} {right} {output}
      ({aux}) four satisfied (by decide) (by decide)
'''
            replacement=f'''    simpa only [mul_comm] using (Compiler.checked_product_sound rho rows {right} {left} {output}
      ({aux}) four satisfied (by decide) (by decide))
'''
            if source.count(original)!=1:raise rk.relation.RelationError('RK subgroup swapped cone generator shape')
            source=source.replace(original,replacement)
    return source


def generate_native_completion(data, accepted_roles, extracted):
    """Derive all original assertions from an independently admitted SDK point.

    The point/subgroup/nonidentity premises describe the externally admitted
    public key, not a circuit output. Global full-group and canonical byte
    contracts remain explicit. Every materialized row is constructed first;
    independent cone soundness then links the exact captured source operands
    to the native witness bundle without assuming row satisfaction.
    """
    plan=completion_plan(data,accepted_roles,extracted);selected=cone_selection(data,accepted_roles,extracted)
    state=plan['state'];obj=state['metadata'];copy=obj['constant_copy'];raw=plan['raw']
    name=lambda h:'cwn'[h[0]]+str(h[1])
    lc=lambda h:linear(state['derived'][h])
    pre=state['inputs'][2:4];inv=state['formulas']['inverse_witnesses'];xinverse=state['nonidentity'][1]
    slots=[(3+pre[0][1],'q.x'),(3+pre[1][1],'q.y')]
    slots += [(3+h[1],f'GroupNativeSubgroupWitness.sharedInverse (C.coefficientD : F) {p}')
              for h,p in zip(inv,('q','twice','four'))]
    slots.append((3+xinverse[1],'public.x⁻¹'))
    witnesses=[c for c,_ in slots];caller=[c for c in plan['kept'] if c not in witnesses]
    def cone_defs(index):
        cone=selected['cones'][index];prefix=cone['role'].replace('.','_')
        return ','.join('C.'+prefix+'_'+identity for identity in cone['inputs']+[cone['output']])
    out=['''import ShielddSecurity.RuntimeTransferRkSubgroupMaterialization
import ShielddSecurity.RuntimeTransferRkSubgroupCones
import ShielddSecurity.GroupNativeSubgroupWitness
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferRkSubgroupCompletion
''',f'-- Accepted metadata identity: {hashlib.sha256(data).hexdigest()}; relation: {obj["relation_digest"]}\n',
         '-- Fresh diagnostic candidate. Runtime codec/SDK embedding interpretation and full caller composition remain open.\n',
         f'def witnessColumns : List Nat := {witnesses}\n',
         'def callerColumns : List Nat := M.kept.filter (fun column => decide (column ∉ witnessColumns))\n',
         'def rawRows : List Row := ['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(raw))+']\n',
         '''def witnessValues {F : Type} [Field F] (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (public : Group.Point F) (column : Nat) : F :=
  let q := GroupNativeCofactor.nativePreimage (C.coefficientD : F) codec writer public
  let twice := GroupFixedWindows.nativeAdd (C.coefficientD : F) q q
  let four := GroupFixedWindows.nativeAdd (C.coefficientD : F) twice twice
''','  '+''.join(f'if column = {c} then {v} else\n  ' for c,v in slots)+'0\n',
         '''def witnessBase {F : Type} [Field F] (base : Nat → F)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (public : Group.Point F) := patchAssignment base (witnessValues codec writer public) witnessColumns
def assignment {F : Type} [Field F] (base : Nat → F)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (public : Group.Point F) := M.assignment (witnessBase base codec writer public)
theorem materialization_rows : C.rawRows = M.rawRows := rfl
theorem caller_columns_kept : ∀ column ∈ callerColumns, column ∈ M.kept ∧ column ∉ witnessColumns := by
  intro column member
  have filtered := List.mem_filter.mp member
  exact ⟨filtered.1, of_decide_eq_true filtered.2⟩
theorem caller_preserved {F : Type} [Field F] (base : Nat → F)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (public : Group.Point F) (column : Nat) (member : column ∈ callerColumns) :
    assignment base codec writer public column = base column := by
  have kept := caller_columns_kept column member
  let seed := witnessBase base codec writer public
  have evaluation := M.eval_kept seed [(column,1)] (by
    intro term present
    simp only [List.mem_singleton] at present
    subst term
    exact kept.1)
  have preserved : M.assignment seed column = seed column := by
    simpa only [eval,Int.cast_one,one_mul,add_zero] using evaluation
  change M.assignment seed column = base column
  exact preserved.trans (patchAssignment_preserves base _ witnessColumns column kept.2)
theorem actual_rows_complete {F J : Type} [Field F] [CharP F M.modulus] [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (model : Group.StandardCurveModel J (C.coefficientD : F))
    (imaginary : F) (nonSquare : Group.NoUnitSquare (C.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (base : Nat → F) (point : J) (subgroup : Scalar.order • point = 0) (nonidentity : point ≠ 0)
    (one : base 0 = 1)
''',f'    (linked : base {copy} = base 0)\n',
         f'    (inputX : eval base {lc(state["inputs"][0])} = (model.coordinates point).x)\n',
         f'    (inputY : eval base {lc(state["inputs"][1])} = (model.coordinates point).y) :\n',
         '''    Satisfies (assignment base codec writer (model.coordinates point)) rawRows ∧
      (∀ column ∈ callerColumns, assignment base codec writer (model.coordinates point) column = base column) := by
  let public := model.coordinates point
  let q := GroupNativeCofactor.nativePreimage (C.coefficientD : F) codec writer public
  let twice := GroupFixedWindows.nativeAdd (C.coefficientD : F) q q
  let four := GroupFixedWindows.nativeAdd (C.coefficientD : F) twice twice
  let eight := GroupFixedWindows.nativeAdd (C.coefficientD : F) four four
  let seed := witnessBase base codec writer public
  let built := M.assignment seed
''',f'''  have seedZero : seed 0 = base 0 :=
    patchAssignment_preserves base _ witnessColumns 0 (by decide)
  have seedCopy : seed {copy} = base {copy} :=
    patchAssignment_preserves base _ witnessColumns {copy} (by decide)
  have seedLink : seed {copy} = seed 0 := seedCopy.trans (linked.trans seedZero.symm)
  have completed := M.materialized_complete seed seedLink
  have materialized : Satisfies built C.rawRows := by rw [materialization_rows]; exact completed.1
  have builtOne : built 0 = 1 := by
    exact (completed.2 0 (by decide)).trans (seedZero.trans one)
  have normalized := Compiler.unoutline_rows_sound built {copy} C.rawRows materialized C.constantLink
''']
    assigned={pre[0]:'q.x',pre[1]:'q.y',xinverse:'public.x⁻¹'}
    assigned.update({h:f'GroupNativeSubgroupWitness.sharedInverse (C.coefficientD : F) {p}'
                     for h,p in zip(inv,('q','twice','four'))})
    for index,h in enumerate(state['inputs'][:2]):
        axis=('x','y')[index]
        out.append(f'''  have public{axis.upper()} : eval built {lc(h)} = public.{axis} := by
    rw [M.eval_kept seed {lc(h)} (by simp [M.kept])]
    simpa [seed,witnessBase,patchAssignment,witnessColumns,eval] using input{axis.upper()}
''')
    for h,value in assigned.items():
        out.append(f'''  have value_{name(h)} : eval built {lc(h)} = {value} := by
    rw [M.eval_kept seed {lc(h)} (by simp [M.kept])]
    simp [seed,witnessBase,patchAssignment,witnessColumns,witnessValues,eval,q,twice,four]
''')
    out.append('''  have native := GroupNativeSubgroupWitness.native_subgroup_constraints codec writer
    (C.coefficientD : F) imaginary model nonSquare imaginarySquare two point subgroup nonidentity
  change Group.OnCurve (C.coefficientD : F) q ∧
    GroupNativeSubgroupWitness.DoubleConstraints (C.coefficientD : F) q ∧
    GroupNativeSubgroupWitness.DoubleConstraints (C.coefficientD : F) twice ∧
    GroupNativeSubgroupWitness.DoubleConstraints (C.coefficientD : F) four ∧
    eight = public ∧ public.x * public.x⁻¹ = 1 at native
''')
    for i,double in enumerate(state['doubles']):
        before=pre if i==0 else state['doubles'][i-1][2:]
        before_point=('q','twice','four')[i];after_point=('twice','four','eight')[i]
        before_values=[f'value_{name(h)}' for h in before]
        for axis,k in (('x',0),('y',1)):
            out.append(f'''  have value_{name(double[k+2])} : eval built {lc(double[k+2])} = {after_point}.{axis} := by
    have formula := C.double{i}_after_{axis}_sound built builtOne materialized
    dsimp only [{cone_defs(3+3*i+k)}] at formula
    rw [{','.join(before_values+[f'value_{name(inv[i])}'])}] at formula
    exact formula
''')
    out.append('  have curveLeft := C.curve_left_sound built builtOne materialized\n')
    out.append('  have curveRight := C.curve_right_sound built builtOne materialized\n')
    for role,i in (('curveLeft',0),('curveRight',1)):
        out.append(f'  dsimp only [{cone_defs(i)}] at {role}\n')
        out.append(f'  rw [value_{name(pre[0])},value_{name(pre[1])}] at {role}\n')
    out.append(f'''  have curveEquation : eval built {lc(state['curve'][0])} = eval built {lc(state['curve'][1])} := by
    rw [curveLeft,curveRight]
    exact native.1
''')
    equations={'curve':'curveEquation'}
    for k,axis in enumerate(('x','y')):
        out.append(f'''  have endpoint{axis.upper()} : eval built {lc(state['inputs'][k])} = eval built {lc(state['doubles'][-1][k+2])} := by
    rw [public{axis.upper()},value_{name(state['doubles'][-1][k+2])},native.2.2.2.2.1]
''')
        equations['rk-link.'+str(k)]='endpoint'+axis.upper()
    product_nodes=state['formulas']['inverse_assert_products']+[state['nonidentity_product']]
    for i,h in enumerate(product_nodes):
        _,left,right=state['nodes'][h]
        cert=arithmetic.product_certificate(state['derived'][left],state['derived'][right],state['derived'][h],plan['normalized'])
        if cert.get('swapped'):left,right=right,left
        out.append(f'''  have inverseProduct{i} := Compiler.checked_product_sound built C.rows
    {lc(left)} {lc(right)} {lc(h)} {linear(cert['auxiliary'])}
    (C.fourNonzero (F := F)) normalized (by decide) (by decide)
  have inverseEquation{i} : eval built {lc(h)} = eval built [(0,1)] := by
    rw [inverseProduct{i}]
''')
        if i<3:
            out.append(f'''    have denominator := C.double{i}_denominator_sound built builtOne materialized
    dsimp only [{cone_defs(2+3*i)}] at denominator
    rw [value_{name(state['doubles'][i][0])},value_{name(state['doubles'][i][1])}] at denominator
    rw [value_{name(inv[i])},denominator]
    simpa only [eval,builtOne,Int.cast_one,one_mul,add_zero] using
      (mul_comm (GroupNativeSubgroupWitness.sharedInverse (C.coefficientD : F) {('q','twice','four')[i]})
        ((1 + Group.delta (C.coefficientD : F) {('q','twice','four')[i]} {('q','twice','four')[i]}) *
          (1 - Group.delta (C.coefficientD : F) {('q','twice','four')[i]} {('q','twice','four')[i]}))).trans
        native.{('2.1','2.2.1','2.2.2.1')[i]}.1
''')
        else:
            out.append(f'''    rw [value_{name(xinverse)},publicX]
    simpa only [eval,builtOne,Int.cast_one,one_mul,add_zero,mul_comm] using native.2.2.2.2.2
''')
        equations['inverse-assert.'+str(i)]='inverseEquation'+str(i)
    out.append(f'''  have builtLink : built {copy} = built 0 := by
    exact (completed.2 {copy} (by decide)).trans
      (seedLink.trans (completed.2 0 (by decide)).symm)
  constructor
  · intro actual member
    simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with '''+' | '.join('rfl' for _ in raw)+'\n')
    byrow={plan['roles'][r]:r for r in plan['assertions']}
    expected_pairs=[(state['curve'][0],state['curve'][1])]+[(state['inputs'][i],state['doubles'][-1][i+2]) for i in range(2)]
    assertion_lcs={r:(lc(a),lc(b)) for r,(a,b) in zip(plan['assertions'][:3],expected_pairs)}
    assertion_lcs.update({'inverse-assert.'+str(i):(lc(h),'[(0,1)]') for i,h in enumerate(product_nodes)})
    for index in sorted(raw):
        if index in plan['materialization_rows']:
            out.append('    · exact completed.1 _ (by decide)\n')
        else:
            role=byrow[index];a,b=assertion_lcs[role];rowa=linear(raw[index][0]);rowb=linear(raw[index][1])
            # Exact signs are retained; both orientation variants square to zero.
            equation=rk.combine(state['derived'][expected_pairs[plan['assertions'].index(role)][0]],
                                state['derived'][expected_pairs[plan['assertions'].index(role)][1]],-1) if role in plan['assertions'][:3] else rk.combine(state['derived'][product_nodes[int(role[-1])]],[(0,1)],-1)
            positive=plan['normalized'][index][0]==equation
            target=f'Compiler.subtract {a} {b}' if positive else f'Compiler.subtract {b} {a}'
            out.append(f'''    · change Square (eval built {rowa}) (eval built {rowb})
      rw [← Compiler.eval_unoutline built {copy} {rowa} builtLink,
        Compiler.canonical_equal built (Compiler.unoutline {copy} {rowa}) ({target}) (by decide),
        Compiler.eval_subtract,{equations[role]}]
      simp [Square,eval]
''')
    out.append('''  · intro column member
    exact caller_preserved base codec writer public column member
''')
    out.append(_audits('',('materialization_rows','caller_columns_kept','caller_preserved','actual_rows_complete')))
    out.append('end ShielddSecurity.RuntimeTransferRkSubgroupCompletion\n')
    return re.sub(r'\bpublic\b', 'publicPoint', ''.join(out)).replace('M.','RuntimeTransferRkSubgroupMaterialization.').replace('C.','RuntimeTransferRkSubgroupCones.')
