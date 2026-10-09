"""Actual-row certificates for the distinct balance129 variable-window lane.

This consumes a checked balance page and independently replayed original rows.
It keeps the 252-bit ownership matcher unchanged: the odd first pair is the
actual [bit128, native false] pair. Certificates alone prove neither denominator
legality nor a native point endpoint. Kernel constructors must still check the
retained exact rows and preserve every shared input and preceding window.
"""
from . import transfer_balance_variable as variable
from . import transfer_ownership as ownership, transfer_relation as relation
from . import transfer_arithmetic as arithmetic
from .transfer_ownership_completion import _square
from .transfer_balance_rows import canonical, combine


def cone_certificates(checked, extracted, window_offset=0, include_precompute=True):
    metadata=checked['metadata']
    if (metadata.get('schema')!='shieldd-transfer-balance-variable-v1' or
            metadata.get('bit_width')!=129 or metadata.get('total_windows')!=65):
        raise relation.RelationError('balance completion requires distinct129 schema')
    relation.natural(window_offset,metadata['window_count'])
    if type(include_precompute)is not bool:
        raise relation.RelationError('balance completion typed precompute flag')
    identity=extracted.get('identity',{})
    if any(identity.get(key)!=metadata[wanted] for key,wanted in
           [('relation_digest','relation_digest'),('stored_rows','full_rows'),('domain_size','domain_size')]):
        raise relation.RelationError('balance completion original row identity')
    selected=extracted.get('selected_rows')
    if not isinstance(selected,list) or not 1<=len(selected)<=8192:
        raise relation.RelationError('balance completion bounded selected rows')
    raw={};previous=-1;copy=metadata['constant_copy']
    for row in selected:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:
            raise relation.RelationError('balance completion row schema')
        index=relation.natural(row['row'],metadata['full_rows'])
        if index<=previous:raise relation.RelationError('balance completion exact ordered rows')
        previous=index
        for terms in (row['a'],row['b']):relation.terms(terms,metadata['domain_size'])
        raw[index]=tuple(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
    table={};squared={}
    for index,row in raw.items():
        a,b=(canonical((0 if c==copy else c,v) for c,v in lc) for lc in row)
        table.setdefault((a,b),[]).append(index);squared.setdefault(a,[]).append((b,index))
    link=(canonical([(0,1),(copy,-1)]),())
    links=[index for index,row in raw.items() if row==link]
    if len(links)!=1:raise relation.RelationError('balance completion unique original constant link')
    matched=variable.match_formulas(checked)
    source=matched['source'];used=set(links);observations={}
    def name(handle):return 'cwn'[handle[0]]+str(handle[1])
    for handle,terms in checked['derived'].items():observations[name(handle)]=('linear',terms)
    indices=list(range(8)) if include_precompute else []
    indices+=list(range(8+14*window_offset,8+14*(window_offset+1)))
    cones=[]
    for ordinal in indices:
        cone=matched['cones'][ordinal]
        graph,roles=ownership.expected_formula(cone['kind'],cone['axis'],cone['inputs'])
        inputs=[name(handle) for handle in roles]
        local_source=source
        if cone['output'][0]=='native':
            output='native_'+str(ordinal);value=cone['output'][1]
            local_source={output:dict(kind='constant',value=value)}
            observations[output]=('linear',canonical([(0,value)]));identities={output}
        else:
            output=name(cone['output'][1]);identities={identity for _,identity in cone['pairs']}
        ordered=[];visited=set()
        def visit(identity):
            if identity in visited:return
            visited.add(identity);node=local_source[identity]
            if identity not in inputs and node['kind'] in ('add','mul'):
                visit(node['left']);visit(node['right'])
            ordered.append(identity)
        for identity in inputs:visit(identity)
        visit(output)
        if visited!=identities|set(inputs):
            raise relation.RelationError('balance completion exact local source closure')
        certificates={}
        for identity in ordered:
            node=local_source[identity];out=observations[identity][1]
            if identity in inputs:certificate=dict(kind='input')
            elif node['kind']=='constant':certificate=dict(kind='constant',coefficient=node['value'])
            elif node['kind']=='add':certificate=dict(kind='add')
            else:
                left,right=(observations[node[side]][1] for side in ('left','right'))
                constants=[(side,lc[0][1] if lc else 0) for side,lc in [('left',left),('right',right)]
                           if all(column==0 for column,_ in lc)]
                if constants:
                    side,value=constants[0];certificate=dict(kind='folded_'+side,coefficient=value)
                elif left==right:
                    rows=table.get((left,out),[])
                    if len(rows)!=1:raise relation.RelationError('balance completion unique exact square row')
                    certificate=dict(kind='square',rows=rows)
                else:
                    minus,plus=combine(left,right,-1),combine(left,right)
                    pairs=[(first,second,aux) for aux,first in squared.get(minus,[])
                           for second in table.get((plus,combine(aux,out,4)),[])]
                    if len(pairs)!=1:raise relation.RelationError('balance completion unique exact product pair')
                    first,second,aux=pairs[0]
                    certificate=dict(kind='product',rows=[first,second],auxiliary=aux)
                used.update(certificate.get('rows',[]))
            certificates[identity]=certificate
        cones.append(dict(role='formula'+str(ordinal),source=local_source,inputs=inputs,
            output=output,ordered=ordered,certificates=certificates,expected_graph=graph))
    # The quotient checker uses only exact LC/product/assertion rows and local
    # quotient ordinals. It has no 252-bit selector calculation or native truth.
    quotients=ownership.quotient_certificates(checked,extracted,window_offset,include_precompute)
    return dict(outline=copy,rows={index:raw[index] for index in sorted(used)},
        cones=cones,observations=observations,quotients=quotients,
        metadata_sha256=checked['metadata_sha256'],
        qualification_parent_sha256=checked.get('qualification_parent_sha256'),
        scope='exact bounded129 source/LC/original rows only; constructor/curve/freshness/native endpoint OPEN')


def product_steps(certificate):
    """Construct fresh pivots for every nonfolded cone materialization.

    Quotient writes and protected columns are deliberately not inferred here;
    a following point/window constructor must sequence them in source order.
    Refusal preserves unsupported shapes rather than guessing output columns.
    """
    copy=certificate['outline'];normalized={index:tuple(canonical((0 if c==copy else c,v)
        for c,v in terms) for terms in row) for index,row in certificate['rows'].items()}
    steps=[];seen={}
    def source_order(cone):
        ordinal=int(cone['role'].removeprefix('formula'))
        if ordinal<8:return (0,ordinal)
        window,local=divmod(ordinal-8,14)
        # Existing runtime computes selection BEFORE the addition. Formula
        # certificates list addition operands first, so order its two actual
        # selector materializations before those four addition expressions.
        rank=local if local<8 else local-4 if local>=12 else local+2
        return (window+1,rank)
    for cone in sorted(certificate['cones'],key=source_order):
        for identity in cone['ordered']:
            proof=cone['certificates'][identity]
            if proof['kind'] not in ('product','square'):continue
            node=cone['source'][identity]
            left,right=(certificate['observations'][node[side]][1] for side in ('left','right'))
            out=certificate['observations'][identity][1]
            if proof['kind']=='product':
                stage=arithmetic.product_completion_certificate(left,right,out,proof,normalized)
                if stage is None:raise relation.RelationError('balance completion unsupported actual product pivots')
                stage=dict(kind='product',**stage)
            else:
                occupied={0,*(column for column,_ in left)}
                pivots=[column for column,value in out if value==1 and column not in occupied]
                if len(pivots)!=1:raise relation.RelationError('balance completion unique fresh actual square pivot')
                pivot=pivots[0]
                stage=dict(kind='square',input=left,output=pivot,
                    remainder=tuple(term for term in out if term[0]!=pivot),rows=proof['rows'])
            key=tuple(stage['rows'])
            if key in seen:
                if seen[key]!=stage:raise relation.RelationError('balance completion shared row materialization drift')
            else:seen[key]=stage;steps.append(stage)
    return dict(steps=steps,scope='source-ordered cone square/product pivots only; quotient/topology/freshness/window construction OPEN')


def window_plan(checked,extracted,window_offset=0,include_precompute=True,readonly_lcs=()):
    """Sequence exact owned point writes; preserve every local shared role.

    Legal affine denominators, curve facts, native meaning and prior-row truth
    are separate proof obligations. This plan infers no such facts from the
    source graph or a desired coordinate. All physical pivots come from the
    replayed original rows, and every unsupported shape is a refusal.
    """
    certificates=cone_certificates(checked,extracted,window_offset,include_precompute)
    quotients=certificates['quotients'];metadata=checked['metadata'];copy=metadata['constant_copy']
    if not isinstance(readonly_lcs,(tuple,list)) or len(readonly_lcs)>4096:
        raise relation.RelationError('balance completion bounded readonly roles')
    protected={0,1,2,6,copy}
    for terms in readonly_lcs:
        if not isinstance(terms,(tuple,list)) or len(terms)>4096:
            raise relation.RelationError('balance completion bounded readonly LC')
        for term in terms:
            if not isinstance(term,(tuple,list)) or len(term)!=2:
                raise relation.RelationError('balance completion readonly term')
            column,coefficient=term;relation.natural(column,metadata['domain_size'])
            if type(coefficient)is not int or not 0<coefficient<relation.MODULUS:
                raise relation.RelationError('balance completion readonly coefficient')
            protected.add(column)
        if canonical(terms)!=tuple(map(tuple,terms)):
            raise relation.RelationError('balance completion canonical readonly roles')
    raw={row['row']:tuple(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
         for row in extracted['selected_rows']}
    normalized={index:tuple(canonical((0 if c==copy else c,v) for c,v in terms)
        for terms in row) for index,row in raw.items()}
    observed=lambda value:checked['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    for point in (checked['points']['base'],checked['windows'][window_offset][0]):
        for value in point:protected.update(column for column,_ in observed(value))
    if not include_precompute:
        for point in (checked['points']['twice'],checked['points']['triple']):
            for value in point:protected.update(column for column,_ in observed(value))
    for handle in checked['bits']:
        protected.update(column for column,_ in checked['derived'][handle])
    for handle in (checked['negative'],checked['magnitude']):
        protected.update(column for column,_ in observed(handle))
    cones={cone['role']:cone for cone in certificates['cones']}
    quotient_by_role={item['role']:item for item in quotients['certificates']}
    stages=[];owned=set();covered=set();read_support=set();seen=set();folded=[];unique={}
    def append(stage,role):
        writes=({stage['output']} if stage['kind'] in ('square','linear') else
                {stage['output'],stage['auxiliary']} if stage['kind']=='product' else
                {stage['quotient'],stage['product'],stage['auxiliary']})
        key=tuple(stage['rows'])
        if key in unique:
            if unique[key]!=stage:raise relation.RelationError('balance completion shared materialization drift')
            return
        if writes&(protected|owned|read_support):
            raise relation.RelationError('balance completion write aliases shared/prior support: '+role)
        if covered&set(stage['rows']):raise relation.RelationError('balance completion original row ownership overlap')
        unique[key]=dict(stage);owned.update(writes);covered.update(stage['rows']);stages.append(dict(role=role,**stage))
        for index in stage['rows']:
            read_support.update(column for terms in normalized[index] for column,_ in terms)
    def emit_cone(index):
        cone=cones['formula'+str(index)]
        for identity in cone['ordered']:
            proof=cone['certificates'][identity]
            if proof['kind']=='input' or identity in seen:continue
            node=cone['source'][identity];out=certificates['observations'][identity][1]
            if node['kind']=='constant':
                if out!=canonical([(0,node['value'])]):raise relation.RelationError('balance completion constant LC')
            else:
                left,right=(certificates['observations'][node[side]][1] for side in ('left','right'))
                if node['kind']=='add':
                    if out!=combine(left,right):raise relation.RelationError('balance completion add LC')
                elif proof['kind'].startswith('folded_'):
                    arithmetic.product_certificate(left,right,out,normalized);folded.append(identity)
                elif proof['kind']=='square':
                    matches=[i for i,row in normalized.items() if row==(left,out)]
                    if matches!=proof['rows']:raise relation.RelationError('balance completion unique square row')
                    append(_square(left,out,proof,normalized),identity)
                else:
                    difference,total=combine(left,right,-1),combine(left,right)
                    matches=[(i,j) for i,row in normalized.items() if row[0]==difference
                             for j,other in normalized.items() if other==(total,combine(row[1],out,4))]
                    if matches!=[tuple(proof['rows'])]:raise relation.RelationError('balance completion unique product rows')
                    stage=arithmetic.product_completion_certificate(left,right,out,proof,normalized)
                    if stage is None:raise relation.RelationError('balance completion unsupported actual product pivots')
                    append(dict(kind='product',**stage),identity)
            seen.add(identity)
    def emit_quotient(index):
        for axis in range(2):
            role=f'quotient.{index}.{axis}';proof=quotient_by_role[role]
            if proof['kind']=='folded':
                if not proof['rows'] and proof['denominator']==((0,1),) and proof['quotient']==proof['numerator']:
                    folded.append(role);continue
                stage=arithmetic.folded_quotient_completion_certificate(proof,normalized);kind='linear'
            else:stage=arithmetic.completion_certificate(proof,normalized);kind='quotient'
            if stage is None:raise relation.RelationError('balance completion unsupported actual quotient shape: '+role)
            append(dict(kind=kind,**stage),role)
    groups=[(0,4,0),(4,4,1)] if include_precompute else []
    start=8+14*window_offset;point_index=2+3*window_offset
    groups += [(start,4,point_index),(start+4,4,point_index+1),(start+8,6,point_index+2)]
    points=[]
    for first,count,quotient in groups:
        before=len(stages)
        order=list(range(first+4,first+6))+list(range(first,first+4)) if count==6 else range(first,first+count)
        for index in order:emit_cone(index)
        material_end=len(stages);emit_quotient(quotient)
        points.append(dict(index=quotient,formula_start=first,formula_count=count,stage_start=before,
            material_end=material_end,stage_end=len(stages),kind='add' if count==6 or quotient==1 else 'double'))
    links=[index for index,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    demanded=set(certificates['rows'])|set(quotients['rows'])
    if len(links)!=1 or covered|set(links)!=demanded:
        raise relation.RelationError('balance completion exact local original row coverage')
    return dict(window_index=metadata['window_start']+window_offset,include_precompute=include_precompute,
        stages=stages,writes=sorted(owned),protected=sorted(protected),folded=folded,point_groups=points,
        local_rows=sorted(demanded),constant_rows=links,outside_scope_rows=sorted(set(raw)-demanded),
        metadata_sha256=checked['metadata_sha256'],qualification_parent_sha256=checked.get('qualification_parent_sha256'),
        scope='bounded exact129 original-row owned writes and support exclusion only; kernel construction/denominator/curve/prior-frame/native endpoint OPEN')
