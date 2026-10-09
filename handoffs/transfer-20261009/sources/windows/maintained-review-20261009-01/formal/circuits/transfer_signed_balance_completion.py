"""Construct the actual local signed-balance slice from checked source/rows.

The four amount columns are shared inputs. Only sign, magnitude, its129 bits
and the original product/auxiliary columns are owned here. Other rows that read
those writes need a later sequencing proof; this is not full Transfer completion.
"""
import hashlib
from . import transfer_balance_rows as balance,transfer_relation as relation

P=balance.P


def plan(metadata_bytes,stream,expected_relation):
    return _from_checked(metadata_bytes,balance.inspect(metadata_bytes,stream,expected_relation))


def _from_checked(metadata_bytes,checked):
    metadata=relation.record(metadata_bytes)
    if (hashlib.sha256(metadata_bytes).hexdigest()!=checked.get('metadata_sha256') or
            metadata.get('schema')!='shieldd-transfer-balance-inspection-v1' or
            metadata.get('ordinary_full_ordered_rows_equal') is not True or
            checked.get('identity',{}).get('relation_digest')!=metadata.get('relation_digest')):
        raise relation.RelationError('signed completion requires the same checked balance parent')
    handles=metadata['handles'];copy=metadata['constant_copy']
    if len(handles)!=5 or len(checked['products'])!=1:
        raise relation.RelationError('signed completion bounded source shape')
    expressions={tuple(item['source']):tuple((c,int(v,16)) for c,v in item['terms']) for item in metadata['expressions']}
    columns=[item['values'][0][1]+3 for item in handles[:4]]
    negative,magnitude=[key[1]+3 for key in handles[4]['values'][1:3]]
    bits=[key[1]+3 for key in handles[4]['bits']]
    if len(bits)!=129 or len(set(bits))!=129:
        raise relation.RelationError('signed completion exact129 distinct source bits')
    product=checked['products'][0]
    node=next((n for n in metadata['nodes'] if n['index']==product['node']),None)
    if node is None or node['multiply'] is not True:
        raise relation.RelationError('signed completion exact original product node')
    left,right=expressions[tuple(node['left'])],expressions[tuple(node['right'])]
    target=expressions[(2,product['node'])]
    if len(target)!=1 or target[0][1]!=1:
        raise relation.RelationError('signed completion unit materialized product required')
    output=target[0][0]
    raw={row['row']:row for row in checked['selected_rows']}
    if len(product['rows'])!=2 or any(index not in raw for index in product['rows']):
        raise relation.RelationError('signed completion original product rows missing')
    minus,plus=[raw[index] for index in product['rows']]
    decode=lambda terms:tuple((c,int(v,16)) for c,v in terms)
    auxiliaryTerms=decode(minus['b'])
    if len(auxiliaryTerms)!=1 or auxiliaryTerms[0][1]!=1:
        raise relation.RelationError('signed completion unit original auxiliary required')
    auxiliary=auxiliaryTerms[0][0]
    unoutline=lambda terms:balance.canonical((0 if c==copy else c,n) for c,n in terms)
    if (unoutline(decode(minus['a']))!=balance.combine(left,right,-1) or
            unoutline(decode(plus['a']))!=balance.combine(left,right) or
            decode(plus['b'])!=balance.combine(auxiliaryTerms,target,4)):
        raise relation.RelationError('signed completion exact original minus/plus constructor')
    if any(c not in (0,negative,magnitude) for c,_ in (*left,*right)):
        raise relation.RelationError('signed completion product has unowned source operand')
    writes=[negative,magnitude,*bits,output,auxiliary]
    shared=[0,1,2,copy,*columns,*[key[1]+3 for h in handles[:4] for key in h['bits']]]
    if len(writes)!=len(set(writes)) or set(writes)&set(shared):
        raise relation.RelationError('signed completion writes overlap shared amount/constant columns')
    roles={role:item['row'] for item in checked['templates'] for role in item['roles']}
    names=['constant-copy','negative.boolean','signed.equation','range4.reconstruction',
           *['range4.boolean'+str(i) for i in range(129)]]
    if any(name not in roles for name in names):
        raise relation.RelationError('signed completion missing original owned row')
    indices=sorted(set([roles[name] for name in names]+product['rows']))
    if len(indices)!=135:
        raise relation.RelationError('signed completion exact135 local original rows')
    if any(index not in raw for index in indices):
        raise relation.RelationError('signed completion original selected row missing')
    for row in (raw[i] for i in indices):
        if any(c not in set(writes)|{0,copy}|set(columns) for c,_ in (*decode(row['a']),*decode(row['b']))):
            raise relation.RelationError('signed completion row has unsupported shared dependency')
    return dict(metadata_sha256=checked['metadata_sha256'],identity=checked['identity'],copy=copy,
        amounts=columns,negative=negative,magnitude=magnitude,bits=bits,product=output,auxiliary=auxiliary,
        product_left=left,product_right=right,owned_writes=writes,preserved_source_columns=shared,
        selected_expression=expressions[tuple(handles[4]['values'][3])],
        difference_expression=expressions[tuple(handles[4]['values'][0])],roles=roles,
        original_row_indices=indices,raw_rows=[raw[i] for i in indices],
        scope='actual135 original local signed rows only; shared4amounts preserved; other rows survival/fullTransfer OPEN')


def construct(recipe,base,amounts):
    if len(amounts)!=4 or any(type(n) is not int or not 0<=n<2**128 for n in amounts):
        raise relation.RelationError('signed completion requires four native u128 inputs')
    if base.get(0)!=1 or base.get(recipe['copy'])!=1:
        raise relation.RelationError('signed completion requires linked native constant one')
    if any(base.get(c)!=n for c,n in zip(recipe['amounts'],amounts)):
        raise relation.RelationError('signed completion shared amount/native input mismatch')
    inputTotal=amounts[0]+amounts[1];outputTotal=amounts[2]+amounts[3]
    negative=int(inputTotal<outputTotal);magnitude=abs(inputTotal-outputTotal)
    if magnitude>=2**129:raise relation.RelationError('signed native magnitude bound failed')
    rho=dict(base);rho[recipe['negative']]=negative;rho[recipe['magnitude']]=magnitude
    for index,column in enumerate(recipe['bits']):rho[column]=(magnitude>>index)&1
    evaluate=lambda terms:sum(rho.get(c,0)*n for c,n in terms)%P
    left,right=evaluate(recipe['product_left']),evaluate(recipe['product_right'])
    rho[recipe['product']]=left*right%P;rho[recipe['auxiliary']]=(left-right)**2%P
    for row in recipe['raw_rows']:
        a=tuple((c,int(v,16)) for c,v in row['a']);b=tuple((c,int(v,16)) for c,v in row['b'])
        if evaluate(a)**2%P!=evaluate(b):
            raise relation.RelationError('constructed signed original row failed: '+str(row['row']))
    if any(rho.get(c)!=value for c,value in base.items() if c not in recipe['owned_writes']):
        raise relation.RelationError('signed completion frame failed')
    return dict(assignment=rho,negative=bool(negative),magnitude=magnitude,owned_writes=recipe['owned_writes'],
        original_rows_satisfied=recipe['original_row_indices'],scope=recipe['scope'])
