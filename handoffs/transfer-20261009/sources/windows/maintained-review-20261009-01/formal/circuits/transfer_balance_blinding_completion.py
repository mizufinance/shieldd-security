"""Exact original-row constructors from genuine VALUE_BLINDING ingress.

Shared neutral fixed renderers receive checked LCs/rows/footprints, never an
invented spend or EPK metadata object. Canonical scalar and full126/native/final
balance composition require subsequent actual physical-chain certificates.
"""
from . import transfer_fixed_spend as fixed,transfer_arithmetic as arithmetic,transfer_relation as relation
from . import generate_transfer_fixed_spend as renderer
from .transfer_balance_rows import canonical,source_index


def requirements(checked):
    if checked.get('metadata',{}).get('schema')!='shieldd-transfer-balance-blinding-fixed-v1':
        raise relation.RelationError('genuine balance blinding ingress required')
    return fixed._requirements(checked,False)


def selection(checked,extracted):
    if extracted.get('include_canonical') is not False:
        raise relation.RelationError('balance blinding canonical proof must be separately constructed')
    raw,normalized=arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    for (a,b),roles in requirements(checked)[0].items():
        if not any(row==(a,b) or not b and row==(canonical((c,-v) for c,v in a),b) for row in raw.values()):
            raise relation.RelationError('balance blinding exact original row missing: '+roles[0])
    products={role:arithmetic.product_certificate(left,right,out,normalized) for role,left,right,out in checked['products']}
    quotients={role:arithmetic.quotient_certificate(n,d,q,normalized) for role,n,d,q in checked['quotients']}
    return raw,normalized,products,quotients


def completion_plan(checked,extracted,*,readonly_lcs=()):
    raw,normalized,products,quotients=selection(checked,extracted)
    obj=checked['metadata'];start=obj['window_start'];count=obj['window_count'];kept={0,1,2,6,obj['constant_copy']}
    kept.update(c for c,_ in checked['expressions'][source_index(obj['blinding']['source'])])
    for bit in obj['bits']:kept.update(c for c,_ in checked['expressions'][source_index(bit)])
    for lc in (*checked['points'][0][0],*readonly_lcs):
        if canonical(lc)!=tuple(lc) or any(type(c)is not int or not 0<=c<obj['domain_size'] for c,_ in lc):
            raise relation.RelationError('balance blinding readonly LC schema')
        kept.update(c for c,_ in lc)
    initial=set();required={'constant-copy'}|{'boolean'+str(i) for i in range(2*start,2*(start+count))}
    for target,names in requirements(checked)[0].items():
        if set(names)&required:
            index=next((i for i,row in raw.items() if row==target or not target[1] and row==(canonical((c,-v) for c,v in target[0]),target[1])),None)
            if index is None:raise relation.RelationError('balance blinding original copy/bit row missing')
            initial.add(index)
    prior=set(c for i in initial for side in normalized[i] for c,_ in side);covered=set(initial);owned=set();windows=[]
    inputs={role:(left,right,out) for role,left,right,out in checked['products']}
    for index in range(start,start+count):
        stages=[];folded=[];folded_quotients=[]
        for suffix in ('select.0','select.1','xx','yy','sum','xy'):
            role=f'window.{index}.{suffix}';cert=products[role]
            if cert['kind'].startswith('folded_'):
                if cert['rows']:raise relation.RelationError('balance blinding folded product invented rows')
                folded.append(role);continue
            step=arithmetic.product_completion_certificate(*inputs[role],cert,normalized)
            if step is None:raise relation.RelationError('balance blinding unsupported actual product shape: '+role)
            stages.append(dict(kind='product',role=role,**step))
        for axis in range(2):
            role=f'window.{index}.quotient.{axis}';cert=quotients[role]
            if cert['kind']=='folded':
                if not cert['rows'] and cert['denominator']==((0,1),) and cert['quotient']==cert['numerator']:
                    folded_quotients.append(role);continue
                step=arithmetic.folded_quotient_completion_certificate(cert,normalized);kind='linear'
            else:step=arithmetic.completion_certificate(cert,normalized);kind='quotient'
            if step is None:raise relation.RelationError('balance blinding unsupported actual quotient shape: '+role)
            stages.append(dict(kind=kind,role=role,**step))
        for step in stages:
            writes=({step['output']} if step['kind']=='linear' else {step['output'],step['auxiliary']} if step['kind']=='product'
                else {step['quotient'],step['product'],step['auxiliary']})
            if writes&(kept|owned|prior):
                categories={'kept':sorted(writes&kept),'owned':sorted(writes&owned),'prior':sorted(writes&prior),
                            'readonly':sorted(writes&{c for lc in readonly_lcs for c,_ in lc})}
                raise relation.RelationError('balance blinding writes alias scalar/bit/shared/prior support: '
                    f'page_start={start} window={index} role={step["role"]} writes={sorted(writes)} categories={categories}')
            if covered&set(step['rows']):raise relation.RelationError('balance blinding row ownership overlap')
            owned.update(writes);covered.update(step['rows']);prior.update(c for row in step['rows'] for side in normalized[row] for c,_ in side)
        windows.append(dict(index=index,stages=stages,folded_products=folded,folded_quotients=folded_quotients))
    if covered!=set(raw):raise relation.RelationError('balance blinding selected original row coverage incomplete')
    return dict(window_start=start,window_count=count,windows=windows,kept=sorted(kept),writes=sorted(owned),
        initial_rows=sorted(initial),original_rows=sorted(raw),metadata_sha256=checked['metadata_sha256'],
        qualification_parent_sha256=checked.get('qualification_parent_sha256'),
        scope='Actual blinding local writes only; scalar0 legal; canonical252/native126/final balance/full frame OPEN')


def generate_window(checked,extracted,offset=0,*,readonly_lcs=()):
    raw,normalized,products,quotients=selection(checked,extracted)
    plan=completion_plan(checked,extracted,readonly_lcs=readonly_lcs)
    relation.natural(offset,plan['window_count']);index=plan['window_start']+offset;stem=f'RuntimeBalanceBlindingWindow{index:03d}'
    modules=[(stem,renderer.render_window(checked,raw,normalized,products,quotients,offset,stem=stem)),
        (stem+'Completion',renderer.render_window_completion(checked,raw,normalized,plan,offset,stem=stem)),
        (stem+'CurveCompletion',renderer.render_window_complete(checked,plan,offset,stem=stem))]
    return modules
