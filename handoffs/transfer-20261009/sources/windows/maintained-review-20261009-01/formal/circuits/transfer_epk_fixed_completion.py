"""Original-row EPK fixed construction plans, isolated from accepted spend ABI.

Only exact replayed product/quotient/Boolean rows yield stages. Source LC roles
alone produce no witness truth. Point/denominator/scalar legality is discharged
by later seed/curve/fixed constructor proofs, not a desired output premise here.
"""
from . import transfer_epk_fixed as epk, transfer_fixed_spend as fixed, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical,source_index


def requirements(checked):
    return fixed._requirements(checked,False)


def extract_rows(checked,stream):
    """Root-only full ordered relation replay; never called by source drafting tests."""
    obj=checked['metadata'];required,products,squares=requirements(checked)
    extracted=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
        required,products,squares,label='epk-fixed')
    extracted.update(metadata_sha256=checked['metadata_sha256'],include_canonical=False,
        scope='actual fixed EPK materializations/quotients/Boolean rows only; native/scalar/kernel/full frame open')
    return extracted


def selection(checked,extracted):
    if extracted.get('include_canonical') is not False:
        raise relation.RelationError('EPK fixed must use independently owned scalar constructor')
    raw,normalized=arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    for (a,b),roles in requirements(checked)[0].items():
        if not any(row==(a,b) or not b and row==(canonical((c,-v) for c,v in a),b) for row in raw.values()):
            raise relation.RelationError('EPK original selected row missing: '+roles[0])
    products={role:arithmetic.product_certificate(left,right,output,normalized) for role,left,right,output in checked['products']}
    quotients={role:arithmetic.quotient_certificate(n,d,q,normalized) for role,n,d,q in checked['quotients']}
    return raw,normalized,products,quotients


def completion_plan(checked,extracted,accepted_capsules,accepted_roles,*,readonly_lcs=()):
    """Exact owned window writes and earlier-row support; no all-row frame assertion.

    Both public/committed columns, all252 bits, native input scalar, published
    EPK and primary inverse are preserved. Only current computed EPK endpoints
    may overlap a window output; all other typed capsule/caller roles are kept.
    Native/circuit mathematical EPK equality is a conclusion for future proofs.
    """
    raw,normalized,products,quotients=selection(checked,extracted)
    obj=checked['metadata'];start=obj['window_start'];count=obj['window_count']
    output_handles={source_index(ref['source']) for ref in obj['output'] if 'source' in ref}
    kept={0,1,2,obj['constant_copy']}
    for owner in (accepted_capsules,accepted_roles):
        if any(owner.get('metadata',{}).get(k)!=obj[k] for k in epk.IDENTITY):
            raise relation.RelationError('EPK constructor exact checked parents required')
        for handle,lc in owner['observed'].items():
            if handle not in output_handles:kept.update(column for column,_ in lc)
    for ref in [obj['randomizer'],obj['inverse'],*obj['published']]:
        if 'source' in ref:kept.update(c for c,_ in checked['expressions'][source_index(ref['source'])])
    for bit in obj['bits']:kept.update(c for c,_ in checked['expressions'][source_index(bit)])
    for lc in checked['points'][0][0]:kept.update(c for c,_ in lc)
    for lc in readonly_lcs:
        if canonical(lc)!=tuple(lc) or any(type(c)is not int or not 0<=c<obj['domain_size'] for c,_ in lc):
            raise relation.RelationError('EPK caller readonly LC schema')
        kept.update(c for c,_ in lc)
    initial=set();required={'constant-copy'}|{'boolean'+str(i) for i in range(2*start,2*(start+count))}
    for target,names in requirements(checked)[0].items():
        if set(names)&required:
            index=next((i for i,row in raw.items() if row==target or not target[1] and row==(canonical((c,-v) for c,v in target[0]),target[1])),None)
            if index is None:raise relation.RelationError('EPK original copy/bit row missing')
            initial.add(index)
    prior=set(c for i in initial for side in normalized[i] for c,_ in side)
    covered=set(initial);owned=set();windows=[]
    product_inputs={role:(left,right,output) for role,left,right,output in checked['products']}
    for index in range(start,start+count):
        stages=[];folded=[];folded_quotients=[]
        for suffix in ('select.0','select.1','xx','yy','sum','xy'):
            role=f'window.{index}.{suffix}';cert=products[role]
            if cert['kind'].startswith('folded_'):
                if cert['rows']:raise relation.RelationError('EPK folded product has invented rows')
                folded.append(role);continue
            step=arithmetic.product_completion_certificate(*product_inputs[role],cert,normalized)
            if step is None:raise relation.RelationError('EPK unsupported original product shape: '+role)
            stages.append(dict(kind='product',role=role,**step))
        for axis in range(2):
            role=f'window.{index}.quotient.{axis}';cert=quotients[role]
            if cert['kind']=='folded':
                if not cert['rows'] and cert['denominator']==((0,1),) and cert['quotient']==cert['numerator']:
                    folded_quotients.append(role);continue
                step=arithmetic.folded_quotient_completion_certificate(cert,normalized);kind='linear'
            else:step=arithmetic.completion_certificate(cert,normalized);kind='quotient'
            if step is None:raise relation.RelationError('EPK unsupported original quotient shape: '+role)
            stages.append(dict(kind=kind,role=role,**step))
        for step in stages:
            writes=({step['output']} if step['kind']=='linear' else
                {step['output'],step['auxiliary']} if step['kind']=='product' else
                {step['quotient'],step['product'],step['auxiliary']})
            if writes&(kept|owned|prior):raise relation.RelationError('EPK original writes alias caller/bit/prior support: '+step['role'])
            if covered&set(step['rows']):raise relation.RelationError('EPK original row ownership overlaps')
            owned.update(writes);covered.update(step['rows'])
            prior.update(c for row in step['rows'] for side in normalized[row] for c,_ in side)
        windows.append(dict(index=index,stages=stages,folded_products=folded,folded_quotients=folded_quotients))
    if covered!=set(raw):raise relation.RelationError('EPK selected original row coverage incomplete')
    return dict(window_start=start,window_count=count,windows=windows,kept=sorted(kept),writes=sorted(owned),
        initial_rows=sorted(initial),original_rows=sorted(raw),metadata_sha256=checked['metadata_sha256'],
        qualification_parent_sha256=checked.get('qualification_parent_sha256'),
        scope='bounded original EPK construction ownership only; scalar/curve/fixed126/native semantics and independent all-row frame OPEN')