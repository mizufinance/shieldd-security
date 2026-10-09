"""Selected canonical balance templates, without source or proof promotion."""
import hashlib
import re
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index, P

ORDER = 6554484396890773809930967563523245729705921265872317281365359162392183254199


def comparison_obligations(steps, bits, endpoint, observed):
    """Check the shared252-step source/LC recurrence; return pending products."""
    if not isinstance(steps,list) or len(steps) != 252:
        raise relation.RelationError('canonical comparator step count')
    previous={'native':f'{1:064x}'}; selected=set(bits)|{endpoint}; products=[]
    for i,step in enumerate(steps):
        if not isinstance(step,list) or len(step)!=6: raise relation.RelationError('canonical step shape')
        before,left,right,factor,product,after=step
        # Validate every reference before Python equality can alias Bool/int handles.
        values=[observed(v) for v in step]
        if before != previous or left != {'source':list(bits[i])}:
            raise relation.RelationError('canonical comparator adjacency/bit order')
        flag=(ORDER-1)>>i & 1
        if right != {'native':f'{flag:064x}'}: raise relation.RelationError('canonical order literal mismatch')
        a,b,_,f,t,z=values
        expected_factor=b if flag else combine([(0,1)],b,-1)
        expected_target=combine(combine(z,b),[(0,1)],-1) if flag else z
        if f!=expected_factor or t!=expected_target:
            raise relation.RelationError('canonical recurrence LC mismatch')
        if a==((0,1),):
            if t!=f: raise relation.RelationError('canonical first folded product mismatch')
        else: products.append((i,a,f,t))
        previous=after
        for v in step:
            if 'source' in v: selected.add(source_index(v['source']))
    if previous != {'source':list(endpoint)}:
        raise relation.RelationError('canonical endpoint/source inventory mismatch')
    return selected,products


def inspect(metadata_bytes, stream, expected_relation):
    if not isinstance(expected_relation,str) or not re.fullmatch('[0-9a-f]{64}',expected_relation):
        raise relation.RelationError('exact canonical expected relation required')
    if len(metadata_bytes) > 2**20:
        raise relation.RelationError('canonical metadata exceeds bound')
    m = relation.record(metadata_bytes)
    required = {'schema','relation_digest','domain_size','stored_rows','ordinary_full_ordered_rows_equal',
                'scope','constant_copy','value','bits','endpoint','steps','expressions','nodes'}
    if set(m) != required or m['schema'] != 'shieldd-transfer-canonical-balance-inspection-v1':
        raise relation.RelationError('canonical metadata schema mismatch')
    if m['scope'] != 'source handles and pre-outline linear combinations only; semantic row certificates remain open':
        raise relation.RelationError('canonical scope mismatch')
    if m['relation_digest'] != expected_relation or m['ordinary_full_ordered_rows_equal'] is not True:
        raise relation.RelationError('canonical identity/noninterference mismatch')
    domain = relation.natural(m['domain_size'],2**32)
    count = relation.natural(m['stored_rows'],domain+1)
    copy = relation.natural(m['constant_copy'],2**32)
    if not 2 < copy < domain: raise relation.RelationError('invalid constant copy')
    value, endpoint = source_index(m['value']), source_index(m['endpoint'])
    if not isinstance(m['bits'],list) or not isinstance(m['steps'],list):
        raise relation.RelationError('canonical bits/steps list required')
    bits = [source_index(bit) for bit in m['bits']]
    if value[0] != 1 or len(bits) != 252 or len(set(bits)) != 252 or value in bits or any(b[0]!=1 for b in bits):
        raise relation.RelationError('canonical witness/bit shape mismatch')
    expressions = {}
    if not isinstance(m['expressions'],list) or len(m['expressions']) > 4096:
        raise relation.RelationError('canonical expression bound exceeded')
    previous_source = None
    for e in m['expressions']:
        if not isinstance(e,dict): raise relation.RelationError('canonical expression object required')
        if set(e) != {'source','terms'}: raise relation.RelationError('canonical expression shape')
        source = source_index(e['source'])
        if previous_source is not None and source <= previous_source:
            raise relation.RelationError('canonical expression ordering')
        previous_source = source
        if source in expressions: raise relation.RelationError('duplicate canonical expression')
        relation.terms(e['terms'],domain)
        lc = tuple((column,int(encoded,16)) for column,encoded in e['terms'])
        if source[0] == 1 and lc != ((3+source[1],1),):
            raise relation.RelationError('canonical witness column mismatch')
        if source[0] == 0 and any(c != 0 for c,_ in lc):
            raise relation.RelationError('canonical constant LC role mismatch')
        expressions[source] = lc
    if not ({value,endpoint}|set(bits)) <= set(expressions):
        raise relation.RelationError('missing canonical value/bit/endpoint expression')
    def observed(v):
        if not isinstance(v,dict) or len(v)!=1: raise relation.RelationError('canonical variable tag')
        if 'source' in v:
            source=source_index(v['source'])
            if source not in expressions: raise relation.RelationError('missing canonical source expression')
            return expressions[source]
        if 'native' in v:
            encoded=v['native']
            if not isinstance(encoded,str) or len(encoded)!=64 or any(c not in '0123456789abcdef' for c in encoded):
                raise relation.RelationError('noncanonical native encoding')
            n=int(encoded,16)
            if n>=P: raise relation.RelationError('native constant outside field')
            return () if n==0 else ((0,n),)
        raise relation.RelationError('unknown canonical variable tag')
    if len(m['steps']) != 252: raise relation.RelationError('canonical comparator step count')
    required_rows, products = {}, []
    def outlined(lc): return canonical([(copy if c==0 else c,v) for c,v in lc])
    def require(role,a,b=()):
        key=(outlined(a),outlined(b)); required_rows.setdefault(key,[]).append(role)
    required_rows[(canonical([(0,1),(copy,P-1)]),())]=['constant-copy']
    for i,bit in enumerate(bits):
        require('boolean'+str(i),expressions[bit],expressions[bit])
    reconstruction=combine([(3+bit[1],2**i) for i,bit in enumerate(bits)],expressions[value],-1)
    require('reconstruction',reconstruction)
    require('committed-link',[(2,1),(3+value[1],P-1)])
    selected_sources,pending = comparison_obligations(m['steps'],bits,endpoint,observed)
    selected_sources.add(value)
    products.extend((i,outlined(combine(a,f,-1)),outlined(combine(a,f)),outlined(t)) for i,a,f,t in pending)
    if set(expressions)!=selected_sources:
        raise relation.RelationError('canonical endpoint/source inventory mismatch')
    require('endpoint',combine(expressions[endpoint],[(0,1)],-1))
    nodes=m['nodes']
    if not isinstance(nodes,list) or len(nodes)>6144: raise relation.RelationError('canonical DAG bound')
    seen=set()
    previous_node=-1
    for node in nodes:
        if not isinstance(node,dict): raise relation.RelationError('canonical node object required')
        if set(node)!={'index','multiply','left','right'} or type(node['multiply']) is not bool:
            raise relation.RelationError('canonical node shape')
        index=relation.natural(node['index'],2**32)
        if index <= previous_node: raise relation.RelationError('canonical node ordering')
        previous_node=index
        if index in seen: raise relation.RelationError('duplicate canonical node')
        seen.add(index)
        for child in [source_index(node['left']),source_index(node['right'])]:
            if child[0]==2 and child[1]>=index: raise relation.RelationError('non-topological canonical DAG')
    node_map = {node['index']:node for node in nodes}
    pending=[endpoint]; reached=set(); roots=set(bits)|{value}
    while pending:
        source=pending.pop()
        if source in roots or source[0]==0: continue
        if source[0]!=2 or source[1] not in node_map:
            raise relation.RelationError('canonical DAG unknown boundary')
        if source[1] in reached: continue
        reached.add(source[1]); node=node_map[source[1]]
        pending.extend([source_index(node['left']),source_index(node['right'])])
    if reached != set(node_map) or any(source[0]==2 and source[1] not in reached for source in selected_sources):
        raise relation.RelationError('canonical DAG closure/source inventory mismatch')
    candidate_as={a for _,minus,plus,_ in products for a in [minus,plus]}
    candidates, matched, rows = {},{},{}
    def observe(row):
        a=tuple((c,int(v,16)) for c,v in row['a']);b=tuple((c,int(v,16)) for c,v in row['b'])
        key = (a,b) if (a,b) in required_rows else (canonical([(c,-v) for c,v in a]),b) if not b else None
        if key in required_rows:
            matched.setdefault(key,row['row']);rows[row['row']]=row
        if a in candidate_as:
            candidates.setdefault(a,[]).append((b,row['row']));rows[row['row']]=row
            if len(candidates[a])>256: raise relation.RelationError('canonical product candidate bound')
    identity=relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['source_blocks'] != [[list(value)]]:
        raise relation.RelationError('canonical value does not match digest-framed committed source role')
    if identity['domain_size']!=domain or identity['stored_rows']!=count:
        raise relation.RelationError('canonical full relation shape mismatch')
    if set(required_rows)-set(matched):
        missing=next(iter(set(required_rows)-set(matched)))
        raise relation.RelationError('missing canonical actual template '+required_rows[missing][0])
    pairs=[]
    for i,minus,plus,out in products:
        pair=next(((x,y) for aux,x in candidates.get(minus,[]) for b,y in candidates.get(plus,[])
                   if b==combine(aux,out,4)),None)
        if pair is None: raise relation.RelationError('missing canonical product pair '+str(i))
        pairs.append({'step':i,'rows':list(pair)})
    indices=set(matched.values())|{i for pair in pairs for i in pair['rows']}
    return {'identity':identity,'metadata_sha256':hashlib.sha256(metadata_bytes).hexdigest(),
            'templates':[{'roles':roles,'row':matched[key]} for key,roles in required_rows.items()],
            'products':pairs,'selected_rows':[rows[i] for i in sorted(indices)],
            'scope':'selected canonical balance row extraction only; raw DAG shape/topology is not a source correspondence proof; kernel/source/API joins open'}


def scoped_canonical_controls(metadata_bytes, checked):
    """Actual selected-row field controls; the rest of Transfer is not evaluated."""
    if hashlib.sha256(metadata_bytes).hexdigest() != checked['metadata_sha256']:
        raise relation.RelationError('canonical controls metadata identity mismatch')
    m=relation.record(metadata_bytes)
    expressions={tuple(e['source']):[(c,int(v,16)) for c,v in e['terms']] for e in m['expressions']}
    rows={r['row']:r for r in checked['selected_rows']}
    roles={role:t['row'] for t in checked['templates'] for role in t['roles']}
    products={p['step']:p['rows'] for p in checked['products']}
    def terms(v):
        return expressions[tuple(v['source'])] if 'source' in v else [(0,int(v['native'],16))]
    def evaluate(lc,rho): return sum(c*rho.get(i,0) for i,c in lc)%P
    def solve(lc,target,rho):
        unknown=[(i,c) for i,c in lc if i not in rho]
        if len(unknown)>1: raise relation.RelationError('canonical control has multiple unknown wires')
        if unknown:
            i,c=unknown[0];rho[i]=(target-evaluate(lc,rho))*pow(c,-1,P)%P
        if evaluate(lc,rho)!=target%P:
            raise relation.RelationError('canonical control equation could not be constructed')
    def encoded(lc): return [(c,int(v,16)) for c,v in lc]
    results=[]
    for name,n,committed,omitted in [('zero',0,0,None),('inclusive-maximum',ORDER-1,ORDER-1,None),
             ('missing-endpoint',ORDER,ORDER,roles['endpoint']),('missing-committed-link',0,ORDER,roles['committed-link'])]:
        rho={0:1,m['constant_copy']:1,3+m['value'][1]:n,2:committed}
        rho.update({3+bit[1]:(n>>i)&1 for i,bit in enumerate(m['bits'])})
        for i,step in enumerate(m['steps']):
            before,left,right,factor,product,after=step
            a,b,f=evaluate(terms(before),rho),evaluate(terms(left),rho),evaluate(terms(factor),rho)
            solve(terms(product),a*f,rho)
            actual=evaluate(terms(after),rho)
            expected=((1-b)*evaluate(terms(right),rho)+a*f)%P
            if actual!=expected: raise relation.RelationError('canonical control source recurrence failed')
            if i in products:
                minus=rows[products[i][0]]
                solve(encoded(minus['b']),evaluate(encoded(minus['a']),rho)**2%P,rho)
        rejected=sorted(index for index,row in rows.items()
            if evaluate(encoded(row['a']),rho)**2%P != evaluate(encoded(row['b']),rho))
        if rejected != ([] if omitted is None else [omitted]):
            raise relation.RelationError('intended canonical selected-row control not observed')
        if omitted is not None and not rho[2]>=ORDER:
            raise relation.RelationError('canonical omission did not violate committed scalar bound')
        results.append({'name':name,'private_value':n,'committed_value':committed,
                        'omitted_original_row':omitted,'original_rejected_rows':rejected,
                        'retained_selected_rows_satisfied':True,'assignment':sorted(rho.items())})
    return {'scope':'selected canonical balance modular-field controls only; full Transfer constraints not evaluated',
            'cases':results}
