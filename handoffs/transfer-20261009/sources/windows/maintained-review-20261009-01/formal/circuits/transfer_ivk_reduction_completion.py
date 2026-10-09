"""Owned comparator/inverse row plans from accepted real IVK reduction roles.

This rechecks retained full-stream selections. It infers only physical compiler
pivots of exact known products; no source handles or caller values are invented.
The final constructor must derive all asserted values from decoded Euclidean
operands, and derive the consumer's nonzero condition from legal ownership.
"""
import hashlib
from . import transfer_ivk_reduction as reduction,transfer_relation as relation,transfer_arithmetic as arithmetic
from .transfer_balance_rows import canonical,combine,source_index


def plan(data,accepted_ivk,extracted,expected_relation,readonly_lcs=()):
    checked=reduction.inspect_metadata(data,accepted_ivk,expected_relation)
    metadata=checked['metadata'];expressions=checked['expressions']
    shape=dict(metadata,full_rows=metadata['stored_rows'])
    raw,normalized=arithmetic.normalize_selection(extracted,shape,hashlib.sha256(data).hexdigest())
    protected={0,metadata['constant_copy']}
    if not isinstance(readonly_lcs,(list,tuple)) or len(readonly_lcs)>4096:
        raise relation.RelationError('bounded IVK reduction readonly inventory')
    for lc in readonly_lcs:
        if not isinstance(lc,(list,tuple)) or len(lc)>4096:
            raise relation.RelationError('IVK reduction canonical readonly LC')
        for term in lc:
            if not isinstance(term,(list,tuple)) or len(term)!=2:
                raise relation.RelationError('IVK reduction readonly term shape')
            column,coefficient=term
            relation.natural(column,metadata['domain_size'])
            if type(coefficient) is not int or not 0<coefficient<relation.MODULUS:
                raise relation.RelationError('IVK reduction readonly term type')
            protected.add(column)
        if canonical(lc)!=tuple(tuple(term) for term in lc):
            raise relation.RelationError('IVK reduction canonical readonly LC')
    observed=lambda value:expressions[source_index(value['source'])] if 'source' in value else canonical([(0,int(value['native'],16))])
    value=lambda key:expressions[source_index(metadata[key])]
    roles={}
    if not isinstance(extracted.get('templates'),list) or not isinstance(extracted.get('products'),list):
        raise relation.RelationError('IVK reduction typed template/product inventories')
    for entry in extracted['templates']:
        if not isinstance(entry,dict) or set(entry)!={'roles','row'} or not isinstance(entry['roles'],list):
            raise relation.RelationError('IVK reduction exact template entries')
        relation.natural(entry['row'],metadata['stored_rows'])
        for role in entry['roles']:
            if not isinstance(role,str) or role in roles or entry['row'] not in raw:
                raise relation.RelationError('IVK reduction duplicate/missing named row')
            roles[role]=entry['row']
    product_roles={}
    for entry in extracted['products']:
        if (not isinstance(entry,dict) or set(entry)!={'role','rows'} or not isinstance(entry['role'],str)
                or entry['role'] in product_roles or not isinstance(entry['rows'],list)):
            raise relation.RelationError('IVK reduction exact product entries')
        for index in entry['rows']:relation.natural(index,metadata['stored_rows'])
        product_roles[entry['role']]=entry['rows']
    selected=set();coverage={}
    def assertion(role,left,right=()):
        index=roles.get(role);target=combine(left,right,-1)
        if index is None or normalized[index] not in ((target,()),(canonical((c,-v) for c,v in target),())):
            raise relation.RelationError('IVK reduction exact assertion '+role)
        selected.add(index);return index
    link=roles.get('constant-copy')
    if link is None or raw[link]!=(canonical([(0,1),(metadata['constant_copy'],-1)]),()):
        raise relation.RelationError('IVK reduction exact global constant link')
    selected.add(link)
    all_owned=set();prior_support=set()
    protected.update(c for key in ('value','quotient','remainder') for c,_ in value(key))
    bit_columns={c for key in ('quotient_bits','remainder_bits') for handle in metadata[key]
        for c,_ in expressions[source_index(handle)]}
    def product(role,left,right,output):
        certificate=arithmetic.product_certificate(left,right,output,normalized)
        if certificate['kind']!='product' or certificate.get('swapped'):
            raise relation.RelationError('IVK reduction owned oriented product '+role)
        if product_roles.get(role)!=certificate['rows']:
            raise relation.RelationError('IVK reduction named physical product mismatch '+role)
        local=arithmetic.product_completion_certificate(left,right,output,certificate,normalized)
        if local is None:raise relation.RelationError('IVK reduction fresh actual product pivots '+role)
        writes={local['output'],local['auxiliary']}
        if writes&(protected|bit_columns|all_owned|prior_support):
            raise relation.RelationError('IVK reduction shared/prior write collision '+role)
        all_owned.update(writes);prior_support.update(c for lc in (left,right,local['remainder']) for c,_ in lc)
        prior_support.update(writes);selected.update(local['rows'])
        for index in local['rows']:
            if index in coverage:raise relation.RelationError('IVK reduction product row reuse')
            coverage[index]=role
        return local
    phases=[]
    for phase,key,width in ((0,'quotient',4),(1,'remainder',252),(2,'remainder',252)):
        bits=[expressions[source_index(handle)] for handle in metadata[key+'_bits']]
        if any(len(lc)!=1 or lc[0][1]!=1 for lc in bits):
            raise relation.RelationError('IVK reduction exact private bit witnesses')
        columns=[lc[0][0] for lc in bits]
        if columns!=list(range(columns[0],columns[0]+width)):
            raise relation.RelationError('IVK reduction exact contiguous private bit allocation')
        stages=[];step_values=[]
        for index,step in enumerate(metadata['steps'][phase]):
            before,left,right,factor,out,after=step
            before,left,factor,out,after=map(observed,(before,left,factor,out,after))
            if index:
                stages.append(product(f'comparison.{phase}.{index}',before,factor,out))
            else:
                if before!=((0,1),) or out!=factor:
                    raise relation.RelationError('IVK reduction actual folded first step')
            step_values.append(dict(before=before,left=left,right=int(right['native'],16),factor=factor,product=out,after=after))
        if phase<2:
            for index,bit in enumerate(bits):
                physical=roles.get(f'{key}.boolean.{index}')
                if physical is None or normalized[physical]!=(bit,bit):
                    raise relation.RelationError('IVK reduction exact Boolean row')
                selected.add(physical)
            assertion(key+'.reconstruction',canonical((c,2**i) for i,c in enumerate(columns)),value(key))
            assertion(key+'_end.assertion',step_values[-1]['after'],((0,1),))
        phases.append(dict(phase=phase,key=key,width=width,start=columns[0],columns=columns,value=value(key),
            stages=stages,steps=step_values))
    assertion('hash-equation',value('equation'),value('value'))
    gate=value('terminal_gate');high=expressions[source_index(metadata['quotient_bits'][3])]
    gate_stage=product('terminal-gate.product',high,combine(((0,1),),phases[2]['steps'][-1]['after'],-1),gate)
    assertion('terminal-gate',gate)
    # The inverse is a quotient of one by the reconstructed consumer. Its
    # denominator legality must be derived in the final owned-input join.
    consumer,inverse=[expressions[source_index(handle)] for handle in metadata['consumer']]
    inverse_certificate=arithmetic.quotient_certificate(((0,1),),consumer,inverse,normalized)
    inverse_plan=arithmetic.completion_certificate(inverse_certificate,normalized)
    if inverse_plan is None:
        # The actual assertion may be one-minus-materialized-product. Preserve
        # its sign explicitly; never rewrite the retained original row record.
        if (inverse_certificate['kind']!='product' or inverse_certificate.get('swapped')
                or len(inverse_certificate['rows'])!=3):
            raise relation.RelationError('IVK reduction actual inverse materialization shape')
        output=inverse_certificate['output'];auxiliary=inverse_certificate['auxiliary']
        if any(len(lc)!=1 or lc[0][1]!=1 for lc in (inverse,output,auxiliary)):
            raise relation.RelationError('IVK reduction exact inverse unit pivots')
        q,p,a=inverse[0][0],output[0][0],auxiliary[0][0]
        writes={q,p,a}
        if len(writes)!=3 or any(c in writes for c,_ in consumer+((0,1),)):
            raise relation.RelationError('IVK reduction inverse pivot/source freshness')
        first,second,third=inverse_certificate['rows']
        expected_pair=[(combine(inverse,consumer,-1),auxiliary),
                       (combine(inverse,consumer),combine(auxiliary,output,4))]
        if [normalized[first],normalized[second]]!=expected_pair:
            raise relation.RelationError('IVK reduction exact original inverse product pair')
        assertion_lc=combine(output,((0,1),),-1)
        reversed_lc=canonical((c,-v) for c,v in assertion_lc)
        if normalized[third] not in ((assertion_lc,()),(reversed_lc,())):
            raise relation.RelationError('IVK reduction inverse original assertion sign')
        inverse_plan=dict(quotient=q,product=p,auxiliary=a,remainder=(),numerator=((0,1),),
            denominator=consumer,rows=inverse_certificate['rows'],assertion_reversed=normalized[third]==(reversed_lc,()))
    else:inverse_plan['assertion_reversed']=False
    if product_roles.get('consumer.inverse')!=inverse_certificate['rows']:
        raise relation.RelationError('IVK reduction actual3-write inverse lowering')
    inverse_writes={inverse_plan['quotient'],inverse_plan['product'],inverse_plan['auxiliary']}
    if inverse_writes&(protected|bit_columns|all_owned|prior_support):
        raise relation.RelationError('IVK reduction inverse write collision')
    selected.update(inverse_certificate['rows'])
    if selected!=set(raw):raise relation.RelationError('IVK reduction exact original row coverage')
    expected_roles={'constant-copy','hash-equation','terminal-gate','quotient.reconstruction','remainder.reconstruction',
        'quotient_end.assertion','remainder_end.assertion',
        *(f'quotient.boolean.{index}' for index in range(4)),*(f'remainder.boolean.{index}' for index in range(252))}
    expected_products={f'comparison.{phase}.{index}' for phase,width in ((0,4),(1,252),(2,252)) for index in range(1,width)}
    expected_products|={'terminal-gate.product','consumer.inverse'}
    if set(roles)!=expected_roles or set(product_roles)!=expected_products:
        raise relation.RelationError('IVK reduction complete named phase inventory')
    return dict(checked=checked,raw=raw,normalized=normalized,roles=roles,phases=phases,
        gate_stage=gate_stage,inverse=inverse_plan,constant_link=link,readonly=sorted(protected),
        source_hash=hashlib.sha256(data).hexdigest(),identity=extracted['identity'],
        scope='actual owned row plans; generic/local constructors and legal consumer nonzero remain to prove')
