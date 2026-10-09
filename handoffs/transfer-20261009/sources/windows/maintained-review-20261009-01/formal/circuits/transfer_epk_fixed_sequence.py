"""Strict six-scope native-seeded ownership and bounded cross-scope fences.

The source plan derives preservation data from every actual original row,
including native bindings/inverses. Native success/Fr/parameter interpretation
are independent semantic inputs; no desired endpoint or row truth is accepted.
"""
from . import transfer_epk_fixed_program as program,transfer_relation as relation
from .generate_hash_round import _signature_audits


def _writes(local):
    scope=local['boundary'];scalar=local['scalar']
    publications=[]
    for terms in scope['published']:
        if len(terms)!=1 or terms[0][1]!=1:raise relation.RelationError('EPK sequence publication witness constructor')
        publications.append(terms[0][0])
    inverse=scope['inverse_constructor']
    return (publications+list(range(scalar['bit_start'],scalar['bit_start']+252))+
        [c for stage in scalar['stages'] for c in (stage['output'],stage['auxiliary'])]+
        local['loop']['writes']+[inverse[key] for key in ('quotient','product','auxiliary')])


def _rows(local):
    rows={}
    def retain(index,row):
        if index in rows and rows[index]!=row:raise relation.RelationError('EPK six-scope shared original row disagreement')
        rows[index]=row
    for extraction in local['selections']:
        for index,row in program.arithmetic.normalize_selection(extraction,
                next(chunk for chunk in local['chunks'] if chunk['metadata_sha256']==extraction['metadata_sha256'])['metadata'],
                extraction['metadata_sha256'])[0].items():retain(index,row)
    # Canonical original rows are supplied to plan() below from the accepted
    # physical derivative. They must agree on the Boolean and copy overlaps.
    for index,row in local['canonical_raw'].items():retain(index,row)
    indices={r for binding in local['boundary']['bindings'] for r in binding['rows']}
    indices.update(local['boundary']['inverse_certificate']['rows'])
    for index in indices:retain(index,local['boundary_raw'][index])
    return rows


def _fence(origin,copy,low,high,writes,prior):
    def covered(column):return column<low or origin<=column<high or column==copy
    exceptions=sorted(c for c in writes if covered(c))
    if len(exceptions)>32:raise relation.RelationError('EPK six-scope bounded32 early native writes')
    support={c for row in prior.values() for terms in row for c,_ in terms}
    if any(not covered(c) or c in exceptions for c in support):
        raise relation.RelationError('EPK six-scope actual prior supports outside numeric fence')
    return dict(origin=origin,copy=copy,low=low,high=high,exceptions=exceptions)


def plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted):
    """Consume genuine row union only; no runtime capture/generation performed."""
    locals=[]
    for scope_id in range(6):
        local=program.plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id)
        certificate=extracted['canonical']['scopes'][scope_id]
        page=local['chunks'][0]
        local['canonical_raw']=program.arithmetic.normalize_selection(certificate,page['metadata'],page['metadata_sha256'])[0]
        locals.append(local)
    copy=locals[0]['checked']['parent']['constant_copy'];writes=[_writes(local) for local in locals]
    protected={0,1,2,6,copy}|{local['scalar']['value'] for local in locals}
    origin=min(c for local in locals for stage in local['scalar']['stages'] for c in (stage['output'],stage['auxiliary']))
    owned=set();prior={};steps=[]
    for scope_id,(local,current) in enumerate(zip(locals,writes)):
        if len(current)!=len(set(current)) or set(current)&(owned|protected):
            raise relation.RelationError('EPK six-scope actual constructor writes overlap shared inputs/earlier scope')
        if any(c in current for row in prior.values() for terms in row for c,_ in terms):
            raise relation.RelationError('EPK six-scope later writes destroy earlier original cone')
        fence=_fence(origin,copy,local['scalar']['bit_start'],
            min(c for stage in local['scalar']['stages'] for c in (stage['output'],stage['auxiliary'])),set(current),prior)
        rows=_rows(local)
        steps.append(dict(scope_id=scope_id,writes=sorted(current),rows=sorted(rows),prior_rows=sorted(prior),fence=fence))
        owned.update(current)
        for index,row in rows.items():
            if index in prior and prior[index]!=row:raise relation.RelationError('EPK six-scope shared original cone row changed')
            prior[index]=row
    return dict(locals=locals,steps=steps,writes=sorted(owned),rows=sorted(prior),protected=sorted(protected),
        parent_sha256=locals[0]['checked']['parent_sha256'],raw_page_sha256=locals[0]['checked']['raw_page_sha256'],
        identity=locals[0]['identity'],scope='Exact six-scope ownership/fences; constructive/native caller/kernel and full Transfer outside frame OPEN')


def generate(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted):
    """Render six-scope composition only after genuine actual ingress succeeds."""
    accepted=plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted)
    return _render(accepted)


def _render(accepted):
    locals=accepted['locals'];steps=accepted['steps'];copy=steps[0]['fence']['copy']
    N=[f'ShielddSecurity.RuntimeTransferEpk{i}NativeBoundary' for i in range(6)]
    A=[f'ShielddSecurity.RuntimeTransferEpk{i}Fixed' for i in range(6)]
    ns='RuntimeTransferEpkSixCompletion'
    bit=lambda i:f'(n ⟨{i},by decide⟩)'
    state=lambda i:f'(stage{i} base model generator n)'
    model='(model : Group.StandardCurveModel J (coefficientD : F))'
    context=f'{{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F) {model} (generator : J) (n : Fin 6 → Nat)'
    out=[''.join(f'import {name}\n' for name in N),
        'import ShielddSecurity.GroupFrameExceptions\n',f'namespace ShielddSecurity.{ns}\n',
        'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
        f'def coefficientD : Int := {A[0]}.coefficientD\ndef sharedInputs : List Nat := {accepted["protected"]}\n',
        'def scalarColumn (scope : Fin 6) : Nat := '+
            ' else '.join(f'if scope.val = {i} then {locals[i]["scalar"]["value"]}' for i in range(5))+
            f' else {locals[5]["scalar"]["value"]}\n',
        'def generatorPoints {F : Type} [Field F] : List (Group.Point F) := ['+','.join(name+'.generator' for name in A)+']\n',
        f'def stage0 {context} : Nat → F := base\n']
    for i in range(6):
        out.append(f'def stage{i+1} {context} : Nat → F := {N[i]}.construct {state(i)} model generator {bit(i)}\n')
        out.append(f'def rows{i} : List Row := {A[i]}.rawRows ++ {N[i]}.inverseRows ++ {N[i]}.bindingRows\n')
        out.append(f'def prefixRows{i+1} : List Row := '+(' ++ '.join(f'rows{j}' for j in range(i+1)))+'\n')
    out.append('def prefixRows0 : List Row := []\n')
    for i in range(6):
        out.append(f'''theorem input_outside{i} (n : Fin 6 → Nat) : ∀ column ∈ sharedInputs,
    column ∉ {N[i]}.totalWrites {bit(i)} := by
  have checked : sharedInputs.all (fun column => decide (column ∉ {N[i]}.totalWrites 0)) = true := by decide
  intro column member
  change column ∉ {N[i]}.totalWrites 0
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
theorem inputs_preserved{i+1} {context} (column : Nat) (member : column ∈ sharedInputs) :
    {state(i+1)} column = base column := by
  exact ({N[i]}.outside_total {state(i)} model generator {bit(i)} column
    (input_outside{i} n column member)).trans '''+
            (f'(inputs_preserved{i} base model generator n column member)\n' if i else 'rfl\n'))
        fence=steps[i]['fence'];frame=f'(⟨{fence["low"]},{fence["high"]}⟩ : GroupFixedCircuitBounds.Frame)'
        if i:
            out.append(f'''theorem write_fence{i} (n : Fin 6 → Nat) :
    GroupFrameExceptions.checkWrites {fence['origin']} {copy} {frame} {fence['exceptions']}
      ({N[i]}.totalWrites {bit(i)}) = true := by
  change GroupFrameExceptions.checkWrites {fence['origin']} {copy} {frame} {fence['exceptions']}
    ({N[i]}.totalWrites 0) = true
  decide
theorem row_fence{i} : GroupFrameExceptions.checkRows {fence['origin']} {copy} {frame}
    {fence['exceptions']} prefixRows{i} = true := by decide
theorem prior_fresh{i} (n : Fin 6 → Nat) : ∀ row ∈ prefixRows{i}, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ {N[i]}.totalWrites {bit(i)} :=
  GroupFrameExceptions.checked_rows {fence['origin']} {copy} {frame} {fence['exceptions']}
    ({N[i]}.totalWrites {bit(i)}) prefixRows{i} (write_fence{i} n) row_fence{i}
''')
    common=f'''{{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) {model} (generator : J) (n : Fin 6 → Nat)
    (positive : ∀ scope, 0 < n scope) (canonical : ∀ scope, n scope < Scalar.order)
    (meaning : ∀ scope, base (scalarColumn scope) = (n scope : F))
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (parameters : ∀ point ∈ (generatorPoints : List (Group.Point F)), point = model.coordinates generator)
    (exactOrder : addOrderOf generator = Scalar.order) (linked : base {copy} = base 0)'''
    args='base model generator n positive canonical meaning one four imaginary nonSquare imaginarySquare parameters exactOrder linked'
    for i in range(6):
        value=locals[i]['scalar']['value']
        out.append(f'theorem complete_prefix{i+1} {common} : Satisfies {state(i+1)} prefixRows{i+1} := by\n')
        if i:
            out.append(f'''  have earlier := complete_prefix{i} {args}
  have retained : Satisfies {state(i+1)} prefixRows{i} := by
    intro row member
    have left := {N[i]}.outside_total_eval {state(i)} model generator {bit(i)} row.a
      (by intro term present; exact prior_fresh{i} n row member term (List.mem_append_left _ present))
    have right := {N[i]}.outside_total_eval {state(i)} model generator {bit(i)} row.b
      (by intro term present; exact prior_fresh{i} n row member term (List.mem_append_right _ present))
    change Square (eval ({N[i]}.construct {state(i)} model generator {bit(i)}) row.a)
      (eval ({N[i]}.construct {state(i)} model generator {bit(i)}) row.b)
    rw [left,right]
    exact earlier row member
''')
        if i:
            out.append(f'''  have inputMeaning := meaning ⟨{i},by decide⟩
  change base {value} = ({bit(i)} : F) at inputMeaning
  have scalarMeaning : {state(i)} {value} = ({bit(i)} : F) :=
    (inputs_preserved{i} base model generator n {value} (by decide)).trans inputMeaning
  have unit : {state(i)} 0 = 1 := (inputs_preserved{i} base model generator n 0 (by decide)).trans one
  have copyLink : {state(i)} {copy} = {state(i)} 0 := by
    rw [inputs_preserved{i} base model generator n {copy} (by decide),
      inputs_preserved{i} base model generator n 0 (by decide),linked]
''')
        else:
            out.append(f'  have scalarMeaning := meaning ⟨0,by decide⟩\n  change base {value} = ({bit(0)} : F) at scalarMeaning\n  have unit := one\n  have copyLink := linked\n')
        out.append(f'''  have current := {N[i]}.cone_rows_complete {state(i)} {bit(i)}
    (positive ⟨{i},by decide⟩) (canonical ⟨{i},by decide⟩) scalarMeaning unit four imaginary
    nonSquare imaginarySquare model generator (parameters {A[i]}.generator (by simp [generatorPoints]))
    exactOrder copyLink
''')
        if i:
            out.append(f'''  intro row member
  change row ∈ prefixRows{i} ++ rows{i} at member
  rcases List.mem_append.mp member with previous | currentRow
  · exact retained row previous
  · exact current row currentRow
''')
        else:out.append('  exact current\n')
    out.append(f'theorem six_cones_complete {common} : Satisfies {state(6)} prefixRows6 :=\n  complete_prefix6 {args}\n')
    audits=([f'input_outside{i}' for i in range(6)]+[f'inputs_preserved{i}' for i in range(1,7)]+
        [name+str(i) for i in range(1,6) for name in ('write_fence','row_fence','prior_fresh')]+
        [f'complete_prefix{i}' for i in range(1,7)]+['six_cones_complete'])
    out.extend('#print axioms '+name+'\n' for name in audits)
    out.append(f'end ShielddSecurity.{ns}\n')
    return _signature_audits(''.join(out))
