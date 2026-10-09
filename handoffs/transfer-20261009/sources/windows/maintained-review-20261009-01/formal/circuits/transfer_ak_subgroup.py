"""Strict bounded AK observer ingress; actual-row/group certificates are separate.

This checks source framing, compiler witness coordinates, the bounded closed
graph and retained affine-expression arithmetic. Nonlinear source coordinates
are not claimed to satisfy their multiplication without actual row checks.
"""
import re
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index

P = relation.MODULUS
SCOPE = 'bounded AK cofactor/on-curve/nonidentity source observation; row and group joins open'


def inspect_metadata(data, expected_relation, expected_ivk_handles):
    if not isinstance(expected_relation, str) or not re.fullmatch('[0-9a-f]{64}', expected_relation):
        raise relation.RelationError('exact canonical AK relation digest required')
    if not isinstance(data, bytes) or len(data) > 1024 * 1024:
        raise relation.RelationError('AK metadata exceeds 1MiB')
    obj = relation.record(data)
    keys = {'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
            'ivk_handles','inputs','curve','doubles','spans','nonidentity','nonidentity_product',
            'expressions','nodes'}
    if set(obj) != keys or obj['schema'] != 'shieldd-transfer-ak-subgroup-v1' or obj['family'] != 'transfer' or obj['scope'] != SCOPE:
        raise relation.RelationError('unknown AK metadata schema/scope')
    if obj['relation_digest'] != expected_relation:
        raise relation.RelationError('AK relation identity mismatch')
    domain, count = relation.natural(obj['domain_size']), relation.natural(obj['full_rows'])
    if domain < 4 or domain & (domain-1) or not 0 < count <= domain:
        raise relation.RelationError('invalid AK relation bounds')
    copy = relation.natural(obj['constant_copy'], domain)
    if copy < 3:
        raise relation.RelationError('invalid AK constant copy')
    def handles(value, length):
        if not isinstance(value, list) or len(value) != length:
            raise relation.RelationError('wrong AK handle collection')
        return tuple(source_index(item) for item in value)
    ivk = handles(obj['ivk_handles'], 4)
    expected = handles(expected_ivk_handles, 4)
    inputs, curve, nonidentity = handles(obj['inputs'], 5), handles(obj['curve'], 2), handles(obj['nonidentity'], 2)
    inverse_product = source_index(obj['nonidentity_product'])
    if ivk != expected or inputs[:2] != ivk[1:3]:
        raise relation.RelationError('AK/accepted IVK input role mismatch')
    if any(tag != 1 for tag,_ in inputs[:4]) or len(set(inputs[:4])) != 4 or inputs[4][0] != 0:
        raise relation.RelationError('AK point/coefficient roles changed')
    if nonidentity[0] != inputs[0] or nonidentity[1][0] != 1 or inverse_product[0] != 2:
        raise relation.RelationError('AK nonidentity role mismatch')
    if not isinstance(obj['doubles'], list) or len(obj['doubles']) != 3 or not isinstance(obj['spans'], list) or len(obj['spans']) != 3:
        raise relation.RelationError('AK requires three bounded doubles')
    doubles = tuple(handles(item,4) for item in obj['doubles'])
    previous = inputs[2:4]
    roots = set(inputs + curve + nonidentity + (inverse_product,))
    end = None
    spans = []
    for double, span in zip(doubles,obj['spans']):
        if double[:2] != previous or any(tag != 2 for tag,_ in double[2:]):
            raise relation.RelationError('AK doubling source chain mismatch')
        if not isinstance(span,list) or len(span) != 2:
            raise relation.RelationError('malformed AK source span')
        start, stop = (relation.natural(value,2**32) for value in span)
        if not start < stop or stop-start > 128 or (end is not None and start != end) or stop != max(i for _,i in double[2:])+1:
            raise relation.RelationError('AK source span boundary mismatch')
        spans.append((start,stop)); end = stop
        roots.update(double); roots.update((2,i) for i in range(start,stop))
        previous = double[2:]
    if any(tag != 2 for tag,_ in curve) or spans[0][0] != max(i for _,i in curve)+1 or inverse_product != (2,end):
        raise relation.RelationError('AK curve/nonidentity allocation boundary mismatch')
    if not isinstance(obj['expressions'],list) or not 1 <= len(obj['expressions']) <= 1024:
        raise relation.RelationError('wrong AK expression collection')
    observed, previous = {}, (-1,-1)
    for item in obj['expressions']:
        if not isinstance(item,dict) or set(item) != {'source','terms'}:
            raise relation.RelationError('malformed AK expression')
        source = source_index(item['source'])
        if source <= previous:
            raise relation.RelationError('noncanonical AK expression order')
        previous = source
        relation.terms(item['terms'],domain)
        terms = tuple((column,int(value,16)) for column,value in item['terms'])
        if any(column == copy for column,_ in terms) or (source[0] == 0 and any(column != 0 for column,_ in terms)):
            raise relation.RelationError('wrong AK constant/outline LC')
        if source[0] == 1 and terms != ((3+source[1],1),):
            raise relation.RelationError('wrong AK compiler witness coordinate')
        observed[source] = terms
    if observed.get(inputs[4]) != ((0,(-10240*pow(10241,-1,P))%P),):
        raise relation.RelationError('wrong Jubjub coefficient')
    if not isinstance(obj['nodes'],list) or len(obj['nodes']) > 2048:
        raise relation.RelationError('wrong AK node collection')
    nodes, previous = {}, -1
    for item in obj['nodes']:
        if not isinstance(item,dict) or set(item) != {'index','multiply','left','right'}:
            raise relation.RelationError('malformed AK source node')
        index = relation.natural(item['index'],2**32)
        left,right = source_index(item['left']),source_index(item['right'])
        if index <= previous or type(item['multiply']) is not bool or any(tag == 2 and child >= index for tag,child in (left,right)):
            raise relation.RelationError('noncanonical AK source topology')
        previous = index; nodes[(2,index)] = (item['multiply'],left,right)
    if nodes.get(inverse_product) != (True,nonidentity[1],nonidentity[0]):
        raise relation.RelationError('wrong existing AK inverse product')
    pending, visited, required = list(roots), set(), set(roots)
    while pending:
        source = pending.pop()
        if source in visited: continue
        visited.add(source)
        if len(visited) > 2048:
            raise relation.RelationError('AK source cone exceeds bound')
        if source[0] == 2:
            if source not in nodes:
                raise relation.RelationError('missing AK source node')
            multiply,left,right = nodes[source]
            if multiply and left[0] != 0 and right[0] != 0: required.update((source,left,right))
            pending.extend((left,right))
        else: required.add(source)
    if set(nodes) != {source for source in visited if source[0] == 2} or set(observed) != required:
        raise relation.RelationError('missing/extra AK graph or expression')
    derived = {}
    for source in sorted(visited):
        if source[0] != 2:
            derived[source] = observed[source]; continue
        multiply,left,right = nodes[source]
        if not multiply:
            value = combine(derived[left],derived[right])
        else:
            value = None
            for const,other in ((derived[left],derived[right]),(derived[right],derived[left])):
                if all(column == 0 for column,_ in const):
                    factor = const[0][1] if const else 0
                    value = canonical((column,coefficient*factor) for column,coefficient in other)
                    break
            if value is None: value = observed[source]
        if source in observed and value != observed[source]:
            raise relation.RelationError('AK affine arithmetic/observed LC mismatch')
        derived[source] = value
    return {'metadata':obj,'inputs':inputs,'curve':curve,'doubles':doubles,'nonidentity':nonidentity,
            'nonidentity_product':inverse_product,'observed':observed,'derived':derived,'nodes':nodes}


def match_formulas(checked):
    """Reuse independent maintained Edwards formulas on the current source DAG."""
    from . import group_rows, poseidon_graph
    def name(handle): return 'cwn'[handle[0]]+str(handle[1])
    source = {}
    for handle, terms in checked['observed'].items():
        if handle[0] == 0:
            source[name(handle)] = {'kind':'constant','value':terms[0][1] if terms else 0}
        elif handle[0] == 1: source[name(handle)] = {'kind':'witness'}
    for handle,(multiply,left,right) in checked['nodes'].items():
        source[name(handle)] = {'kind':'mul' if multiply else 'add','left':name(left),'right':name(right)}
    cones, inverses, assertions = [], [], []
    def match(role, inputs, output):
        graph = group_rows.expected(role)
        try: pairs = poseidon_graph.match_source(graph,source,[name(x) for x in inputs],name(output))
        except ValueError as error: raise relation.RelationError('AK '+role+' source formula mismatch: '+str(error)) from error
        cones.append({'formula':role,'inputs':inputs,'output':output,'graph':graph,'pairs':pairs,'source':source})
    for role,output in zip(('curve.left','curve.right'),checked['curve']):
        match(role,checked['inputs'][2:4],output)
    for double,span in zip(checked['doubles'],checked['metadata']['spans']):
        found = []
        for node,(multiply,left,right) in checked['nodes'].items():
            if not span[0] <= node[1] < span[1] or not multiply or left[0] != 1 or right[0] != 2:
                continue
            try: poseidon_graph.match_source(group_rows.expected('denominator'),source,
                                            [name(x) for x in double[:2]],name(right))
            except ValueError: continue
            found.append((left,right,node))
        if len(found) != 1:
            raise relation.RelationError('AK requires one existing shared inverse per double')
        inverse,denominator,assert_product = found[0]
        inverses.append(inverse); assertions.append(assert_product)
        match('denominator',double[:2],denominator)
        match('x',double[:2]+(inverse,),double[2])
        match('y',double[:2]+(inverse,),double[3])
    witnesses = set(checked['inputs'][:4]+checked['nonidentity'][1:]+tuple(inverses))
    if len(witnesses) != 8 or witnesses != {handle for handle in checked['observed'] if handle[0] == 1}:
        raise relation.RelationError('extra/aliased AK inverse or point witnesses')
    return {'cones':cones,'inverse_witnesses':inverses,'inverse_assert_products':assertions,
            'scope':'current AK source formulas only; actual multiplication/assertion rows remain open'}


def extract(data, expected_ivk_handles, stream, expected_relation):
    """Check every selected nonlinear operation and required assertion against rows."""
    import hashlib
    checked = inspect_metadata(data,expected_relation,expected_ivk_handles)
    formulas = match_formulas(checked)
    m, derived = checked['metadata'], checked['derived']
    copy = m['constant_copy']
    def outline(terms): return canonical((copy if column == 0 else column,value) for column,value in terms)
    required, products = {}, []
    def require(role,a,b=()): required.setdefault((outline(a),outline(b)),[]).append(role)
    required[(canonical([(0,1),(copy,P-1)]),())] = ['constant-copy']
    require('curve',combine(derived[checked['curve'][0]],derived[checked['curve'][1]],-1))
    for axis in range(2):
        require('public-link.'+str(axis),combine(derived[checked['inputs'][axis]],derived[checked['doubles'][-1][axis+2]],-1))
    for index,node in enumerate(formulas['inverse_assert_products']+[checked['nonidentity_product']]):
        require('inverse-assert.'+str(index),combine(derived[node],[(0,1)],-1))
    for source,(multiply,left,right) in checked['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0: continue
        a,b,z = derived[left],derived[right],derived[source]
        role = 'node.'+str(source[1])
        if left == right:
            require(role+'.square',a,z)
        else:
            products.append((role,outline(combine(a,b,-1)),outline(combine(a,b)),outline(z)))
    targets = {a for _,minus,plus,_ in products for a in (minus,canonical((c,-v) for c,v in minus),plus)}
    matched,candidates,rows = {},{},{}
    def observe(row):
        a = tuple((c,int(v,16)) for c,v in row['a'])
        b = tuple((c,int(v,16)) for c,v in row['b'])
        key = (a,b)
        if key not in required: key = (canonical((c,-v) for c,v in a),b)
        if key in required:
            matched.setdefault(key,row['row']); rows[row['row']] = row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row['row'])); rows[row['row']] = row
            if len(candidates[a]) > 128: raise relation.RelationError('AK product candidate bound exceeded')
    identity = relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size'] != m['domain_size'] or identity['stored_rows'] != m['full_rows']:
        raise relation.RelationError('AK ordinary relation shape mismatch')
    missing = set(required)-set(matched)
    if missing: raise relation.RelationError('missing actual AK template '+required[next(iter(missing))][0])
    pairs = []
    for role,minus,plus,out in products:
        pair = next(((x,y) for aux,x in candidates.get(minus,[])+candidates.get(canonical((c,-v) for c,v in minus),[])
                     for b,y in candidates.get(plus,[]) if b == combine(aux,out,4)),None)
        if pair is None: raise relation.RelationError('missing actual AK product '+role)
        pairs.append({'role':role,'rows':list(pair)})
    indices = set(matched.values()) | {index for pair in pairs for index in pair['rows']}
    return {'identity':identity,'metadata_sha256':hashlib.sha256(data).hexdigest(),
            'templates':[{'roles':roles,'row':matched[key]} for key,roles in required.items()],
            'products':pairs,'selected_rows':[rows[i] for i in sorted(indices)],
            'scope':'actual AK row extraction only; arbitrary-assignment kernel/source/group composition remains open'}


def cone_certificates(data, checked, expected_ivk_handles, expected_relation):
    """Adapt current checked rows to the existing bounded cone proof generator."""
    import hashlib
    if checked.get('metadata_sha256') != hashlib.sha256(data).hexdigest():
        raise relation.RelationError('AK cone metadata identity mismatch')
    state = inspect_metadata(data,expected_relation,expected_ivk_handles)
    formulas = match_formulas(state)
    copy = state['metadata']['constant_copy']
    def name(handle): return 'cwn'[handle[0]]+str(handle[1])
    def unoutline(terms): return canonical((0 if c == copy else c,int(v,16)) for c,v in terms)
    raw = {row['row']: (tuple((c,int(v,16)) for c,v in row['a']),tuple((c,int(v,16)) for c,v in row['b']))
           for row in checked['selected_rows']}
    table, squared = {}, {}
    for index,row in sorted(raw.items()):
        a,b = (canonical((0 if c == copy else c,v) for c,v in terms) for terms in row)
        table.setdefault((a,b),index); squared.setdefault(a,[]).append((b,index))
    observations = {name(handle): ('linear',terms) for handle,terms in state['derived'].items()}
    cones = []
    for index,matched in enumerate(formulas['cones']):
        role = matched['formula'] if index < 2 else 'double'+str((index-2)//3)+'.'+('after.' if matched['formula'] in ('x','y') else '')+matched['formula']
        inputs = [name(handle) for handle in matched['inputs']]
        output = name(matched['output'])
        source = matched['source']
        identities = {identity for _,identity in matched['pairs']}
        ordered,visited = [],set()
        def visit(identity):
            if identity in visited: return
            visited.add(identity)
            if identity not in inputs and source[identity]['kind'] in ('add','mul'):
                visit(source[identity]['left']); visit(source[identity]['right'])
            ordered.append(identity)
        visit(output)
        if visited != identities: raise relation.RelationError('AK matched source closure mismatch')
        certificates = {}
        for identity in ordered:
            node = source[identity]; out = observations[identity][1]
            if identity in inputs: certificate = {'kind':'input'}
            elif node['kind'] == 'constant': certificate = {'kind':'constant','coefficient':node['value']}
            else:
                left,right = (observations[node[side]][1] for side in ('left','right'))
                if node['kind'] == 'add': certificate = {'kind':'add'}
                else:
                    constants = [(side,terms[0][1] if terms else 0) for side,terms in (('left',left),('right',right))
                                 if all(column == 0 for column,_ in terms)]
                    if constants:
                        side,coefficient = constants[0]
                        certificate = {'kind':'folded_'+side,'coefficient':coefficient}
                    elif left == right:
                        if (left,out) not in table: raise relation.RelationError('missing exact AK square certificate')
                        certificate = {'kind':'square','rows':[table[(left,out)]]}
                    else:
                        minus,plus = combine(left,right,-1),combine(left,right)
                        candidates = [(first,table[(plus,combine(aux,out,4))],aux) for aux,first in squared.get(minus,[])
                                      if (plus,combine(aux,out,4)) in table]
                        if not candidates: raise relation.RelationError('missing exact oriented AK product certificate')
                        first,second,auxiliary = min(candidates)
                        certificate = {'kind':'product','rows':[first,second],'auxiliary':auxiliary}
            certificates[identity] = certificate
        cones.append({'role':role,'source':source,'inputs':inputs,'output':output,'ordered':ordered,'certificates':certificates})
    return {'outline':copy,'rows':raw,'cones':cones,'observations':observations}


def ingress_controls(data, expected_ivk_handles, expected_relation):
    """Specific current-metadata rejection controls, never semantic row controls."""
    import copy
    import json
    state = inspect_metadata(data,expected_relation,expected_ivk_handles)
    match_formulas(state)
    original = state['metadata']
    cases = []
    for name,reason in [('point-role','AK/accepted IVK input role mismatch'),
                        ('coefficient','wrong Jubjub coefficient'),
                        ('missing-source-node','missing AK source node'),
                        ('nonidentity-operand','wrong existing AK inverse product'),
                        ('last-coordinate-order','AK x source formula mismatch')]:
        value = copy.deepcopy(original)
        if name == 'point-role': value['inputs'][0] = value['inputs'][1]
        elif name == 'coefficient':
            item = next(item for item in value['expressions'] if item['source'] == value['inputs'][4])
            item['terms'][0][1] = f'{(int(item["terms"][0][1],16)+1)%P:064x}'
        elif name == 'missing-source-node':
            value['nodes'] = [node for node in value['nodes'] if node['index'] != value['curve'][0][1]]
        elif name == 'nonidentity-operand':
            node = next(node for node in value['nodes'] if node['index'] == value['nonidentity_product'][1])
            node['right'] = value['inputs'][1]
        else: value['doubles'][-1][2:] = value['doubles'][-1][2:][::-1]
        try:
            mutated = inspect_metadata((json.dumps(value)+'\n').encode(),expected_relation,expected_ivk_handles)
            match_formulas(mutated)
        except relation.RelationError as error:
            if reason not in str(error): raise relation.RelationError('AK control failed for unrelated reason: '+str(error)) from error
            cases.append({'name':name,'observed_rejection':str(error)})
        else: raise relation.RelationError('AK ingress mutant accepted: '+name)
    return {'scope':'AK metadata/formula rejection controls only; not semantic omission evidence','cases':cases}


def scoped_semantic_controls(data, checked, expected_ivk_handles, expected_relation):
    """Construct assignments for the actual AK slice, not the full Transfer."""
    state = inspect_metadata(data,expected_relation,expected_ivk_handles)
    cone_certificates(data,checked,expected_ivk_handles,expected_relation)
    formulas = match_formulas(state)
    d = -10240*pow(10241,-1,P)%P
    order = 6554484396890773809930967563523245729705921265872317281365359162392183254199
    def add(a,b):
        x,y = a; u,v = b; delta = d*x*u*y*v%P
        return ((x*v+y*u)*pow((1+delta)%P,-1,P)%P,
                (y*v+x*u)*pow((1-delta)%P,-1,P)%P)
    def multiply(a,n):
        result = (0,1)
        while n:
            if n&1: result = add(result,a)
            a = add(a,a); n >>= 1
        return result
    def on_curve(a):
        x,y = a; return (y*y-x*x-1-d*x*x*y*y)%P == 0
    q = (3,26155723652191673091881779851507865815856437797311909079256717375290769542325)
    double_points = [q]
    for _ in range(3): double_points.append(add(double_points[-1],double_points[-1]))
    g = double_points[-1]
    if not on_curve(q) or not on_curve(g) or g[0] == 0 or multiply(g,order) != (0,1):
        raise relation.RelationError('AK control independent positive group checks failed')
    rowmap = {row['row']:row for row in checked['selected_rows']}
    roles = {role:item['row'] for item in checked['templates'] for role in item['roles']}
    def terms(items): return tuple((c,int(v,16)) for c,v in items)
    def evaluate(lc,rho): return sum(v*rho.get(c,0) for c,v in lc)%P
    def solve(lc,target,rho):
        missing = [(c,v) for c,v in lc if c not in rho]
        if len(missing) > 1: raise relation.RelationError('AK control has multiple unknown LC columns')
        if missing:
            c,v = missing[0]; rho[c] = (target-evaluate(lc,rho))*pow(v,-1,P)%P
        if evaluate(lc,rho) != target%P: raise relation.RelationError('AK control LC assignment conflict')
    results = []
    for name,point,omitted in [('positive',g,None),('missing-final-y',(g[0],(-g[1])%P),roles['public-link.1'])]:
        source_values = {}
        for handle,value in zip(state['inputs'][:4],point+q): source_values[handle] = value
        for before,inverse in zip(double_points,formulas['inverse_witnesses']):
            delta = d*before[0]**2*before[1]**2%P
            source_values[inverse] = pow((1-delta*delta)%P,-1,P)
        source_values[state['nonidentity'][1]] = pow(point[0],-1,P)
        for handle,lc in state['observed'].items():
            if handle[0] == 0: source_values[handle] = lc[0][1] if lc else 0
        for handle,(is_multiply,left,right) in sorted(state['nodes'].items()):
            source_values[handle] = (source_values[left]*source_values[right] if is_multiply else source_values[left]+source_values[right])%P
        rho = {0:1,state['metadata']['constant_copy']:1}
        for handle,lc in sorted(state['observed'].items()): solve(lc,source_values[handle],rho)
        for product in checked['products']:
            row = rowmap[product['rows'][0]]
            solve(terms(row['b']),evaluate(terms(row['a']),rho)**2%P,rho)
        rejected = sorted(i for i,row in rowmap.items() if evaluate(terms(row['a']),rho)**2%P != evaluate(terms(row['b']),rho))
        if rejected != ([] if omitted is None else [omitted]):
            raise relation.RelationError('intended AK selected-row semantic rejection not observed')
        actual_point = (evaluate(state['observed'][state['inputs'][0]],rho),evaluate(state['observed'][state['inputs'][1]],rho))
        multiple = multiply(actual_point,order)
        if not on_curve(actual_point) or actual_point[0] == 0 or (omitted is None and multiple != (0,1)) or (omitted is not None and multiple != (0,P-1)):
            raise relation.RelationError('AK control intended subgroup predicate not observed')
        results.append({'name':name,'assignment':sorted(rho.items()),'omitted_original_row':omitted,
                        'original_rejected_rows':rejected,'retained_selected_rows_satisfied':True,
                        'point':actual_point,'order_multiple':multiple})
    return {'scope':f'actual {len(rowmap)}-row AK slice modular-field controls; full Transfer constraints not evaluated','cases':results}
