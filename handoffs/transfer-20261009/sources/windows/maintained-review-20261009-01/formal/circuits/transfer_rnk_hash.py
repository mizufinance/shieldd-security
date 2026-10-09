"""Bounded current RNK sponge boundaries; extraction is not qualification."""
import hashlib
import re
import copy
import json
from . import transfer_relation as relation, poseidon_graph
from .transfer_balance_rows import canonical, source_index

P = relation.MODULUS
SCOPE = ('one existing permutation cone; before states are after absorption; '
         'other boundaries have LCs only; semantic joins open')


def inspect_boundaries(data, expected_relation, ivk_handles, expected_rnk_bindings):
    """Check exact framing and all three absorption transitions using actual LCs.

    This does not yet check permutation source cones or their multiplication rows.
    """
    if not isinstance(expected_relation,str) or not re.fullmatch('[0-9a-f]{64}',expected_relation):
        raise relation.RelationError('exact RNK hash relation digest required')
    if not isinstance(ivk_handles,(list,tuple)) or len(ivk_handles) != 4:
        raise relation.RelationError('wrong accepted IVK handle shape')
    ivk_handles = [source_index(list(x)) if isinstance(x,(list,tuple)) else source_index(x) for x in ivk_handles]
    if not isinstance(expected_rnk_bindings,dict):
        raise relation.RelationError('accepted RNK caller bindings required')
    if not isinstance(data, bytes) or len(data) > 4 * 1024 * 1024:
        raise relation.RelationError('RNK hash metadata exceeds 4MiB')
    obj = relation.record(data)
    keys = {'schema','family','scope','relation_digest','domain_size','full_rows',
            'constant_copy','ordinary_full_ordered_rows_equal','block','ivk_handles',
            'hashes','rnk_bindings','expressions','nodes'}
    if (set(obj) != keys or obj['schema'] != 'shieldd-transfer-rnk-hash-block-v1'
            or obj['family'] != 'transfer' or obj['scope'] != SCOPE):
        raise relation.RelationError('unknown RNK hash schema/scope')
    if (obj['relation_digest'] != expected_relation
            or obj['ordinary_full_ordered_rows_equal'] is not True
            or obj['ivk_handles'] != [list(x) for x in ivk_handles]):
        raise relation.RelationError('RNK hash identity/IVK/noninterference mismatch')
    size = relation.natural(obj['domain_size'])
    count = relation.natural(obj['full_rows'])
    copy = relation.natural(obj['constant_copy'], size)
    if size < 4 or size & (size-1) or not 0 < count <= size or copy < 3:
        raise relation.RelationError('invalid RNK hash relation bounds')
    block_index = relation.natural(obj['block'], 3)
    observed = {}
    previous = (-1,-1)
    if not isinstance(obj['expressions'], list) or not 1 <= len(obj['expressions']) <= 4096:
        raise relation.RelationError('invalid RNK hash expression collection')
    for item in obj['expressions']:
        if not isinstance(item, dict) or set(item) != {'source','terms'}:
            raise relation.RelationError('malformed RNK hash expression')
        source = source_index(item['source'])
        if source <= previous:
            raise relation.RelationError('noncanonical RNK hash expression order')
        previous = source
        relation.terms(item['terms'], size)
        lc = tuple((col,int(value,16)) for col,value in item['terms'])
        if any(col == copy for col,_ in lc):
            raise relation.RelationError('outlined RNK hash boundary')
        if source[0] == 1 and lc != ((3+source[1],1),):
            raise relation.RelationError('wrong RNK hash witness projection')
        if source[0] == 0 and any(col != 0 for col,_ in lc):
            raise relation.RelationError('nonconstant RNK hash constant')
        observed[source] = lc
    boundary_sources = set()
    def value(ref):
        if not isinstance(ref, dict) or len(ref) != 1:
            raise relation.RelationError('malformed RNK hash observed value')
        if set(ref) == {'native'}:
            encoded = ref['native']
            if (not isinstance(encoded,str) or len(encoded) != 64
                    or any(c not in '0123456789abcdef' for c in encoded)
                    or int(encoded,16) >= P):
                raise relation.RelationError('noncanonical RNK hash Native value')
            n = int(encoded,16)
            return ((0,n),) if n else ()
        if set(ref) != {'source'}:
            raise relation.RelationError('unknown RNK hash observed value')
        source = source_index(ref['source'])
        if source not in observed:
            raise relation.RelationError('missing RNK hash boundary LC')
        boundary_sources.add(source)
        return observed[source]
    hashes = obj['hashes']
    if not isinstance(hashes,list) or len(hashes) != 2:
        raise relation.RelationError('wrong RNK hash call count')
    parsed = []
    for call,domain,arity,width,blocks in zip(hashes,(17,18),(9,1),(6,3),(2,1)):
        if (not isinstance(call,dict) or set(call) != {'domain','inputs','output','blocks'}
                or type(call['domain']) is not int or call['domain'] != domain
                or not isinstance(call['inputs'],list) or len(call['inputs']) != arity
                or not isinstance(call['blocks'],list) or len(call['blocks']) != blocks):
            raise relation.RelationError('wrong RNK hash domain/arity/blocks')
        inputs = [value(x) for x in call['inputs']]
        output = value(call['output'])
        states = []
        for block in call['blocks']:
            if (not isinstance(block,dict) or set(block) != {'before','after'}
                    or any(not isinstance(block[k],list) or len(block[k]) != width
                           for k in ('before','after'))):
                raise relation.RelationError('wrong RNK permutation state width')
            states.append(([value(x) for x in block['before']],
                           [value(x) for x in block['after']]))
        if output != states[-1][1][1] or call['output'] != call['blocks'][-1]['after'][1]:
            raise relation.RelationError('RNK hash output lane mismatch')
        parsed.append((inputs,output,states))
    inputs,output,states = parsed[0]
    first,second = states
    expected_first = [((0,2321),)] + inputs[:5]
    expected_second = [first[1][0]] + [canonical(first[1][i+1]+inputs[5+i]) for i in range(4)] + [first[1][5]]
    if first[0] != expected_first or second[0] != expected_second:
        raise relation.RelationError('RNK wide absorption LC mismatch')
    ci,co,cs = parsed[1]
    if (ci != [output] or hashes[1]['inputs'] != [hashes[0]['output']]
            or cs[0][0] != [((0,274),), output, ()]):
        raise relation.RelationError('RNK commitment absorption/input mismatch')
    bindings = obj['rnk_bindings']
    if (not isinstance(bindings,dict)
            or set(bindings) != {'inputs','hash','commitment','regulated','registered','effective_nk'}
            or bindings['inputs'] != hashes[0]['inputs']
            or bindings['hash'] != hashes[0]['output']
            or bindings['commitment'] != hashes[1]['output']):
        raise relation.RelationError('RNK caller/hash boundary mismatch')
    if bindings != expected_rnk_bindings:
        raise relation.RelationError('RNK hash/accepted caller role mismatch')
    for key in ('regulated','registered','effective_nk'):
        value(bindings[key])
    value({'source':list(ivk_handles[0])})
    return {'metadata':obj,'observed':observed,'boundary_sources':boundary_sources,
            'states':parsed,'block':block_index,
            'scope':'exact sponge boundary LC checks only; permutation and actual rows open'}


def inspect_metadata(data, parameter_root, expected_relation, ivk_handles, expected_rnk_bindings):
    checked = inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    obj,observed = checked['metadata'],checked['observed']
    block = obj['hashes'][0]['blocks'][checked['block']] if checked['block'] < 2 else obj['hashes'][1]['blocks'][0]
    before,after = block['before'],block['after']
    boundaries = [source_index(x['source']) for x in before if 'source' in x]
    if len(set(boundaries)) != len(boundaries):
        raise relation.RelationError('aliased RNK permutation inputs')
    outputs = [source_index(x['source']) if set(x) == {'source'} else None for x in after]
    if any(x is None for x in outputs):
        raise relation.RelationError('native RNK permutation output')
    nodes,previous = {},-1
    if not isinstance(obj['nodes'],list) or len(obj['nodes']) > 16384:
        raise relation.RelationError('wrong RNK permutation node collection')
    for item in obj['nodes']:
        if not isinstance(item,dict) or set(item) != {'index','multiply','left','right'}:
            raise relation.RelationError('malformed RNK permutation node')
        index = relation.natural(item['index'],2**32)
        if index <= previous or type(item['multiply']) is not bool:
            raise relation.RelationError('noncanonical RNK permutation node ordering/type')
        previous = index
        left,right = source_index(item['left']),source_index(item['right'])
        if any(tag == 2 and child >= index for tag,child in (left,right)):
            raise relation.RelationError('forward RNK permutation edge')
        nodes[(2,index)] = (item['multiply'],left,right)
    visited,pending = set(),list(outputs)
    while pending:
        source = pending.pop()
        if source in visited: continue
        visited.add(source)
        if len(visited) > 16384:
            raise relation.RelationError('RNK permutation cone exceeds finite bound')
        if source in boundaries: continue
        if source[0] == 2:
            if source not in nodes: raise relation.RelationError('missing RNK permutation node')
            multiply,left,right = nodes[source]
            pending.extend((left,right))
        elif source[0] == 0:
            if source not in observed: raise relation.RelationError('missing RNK permutation constant')
        else: raise relation.RelationError('undeclared RNK permutation witness')
    if set(nodes) != {x for x in visited if x[0] == 2 and x not in boundaries}:
        raise relation.RelationError('extra RNK permutation nodes')
    required = checked['boundary_sources'] | {x for x in visited if x[0] == 0}
    for source,(multiply,left,right) in nodes.items():
        if multiply and left[0] != 0 and right[0] != 0:
            required.update((source,left,right))
    if set(observed) != required:
        raise relation.RelationError('missing/extra RNK selected expression')
    names = {x:f'w{i}' for i,x in enumerate(boundaries)}
    def name(x): return names.get(x,'cwn'[x[0]]+str(x[1]))
    abstract = {names[x]:{'kind':'witness'} for x in boundaries}
    derived = {x:observed[x] for x in boundaries}
    for source in sorted(visited):
        if source in boundaries: continue
        if source[0] == 0:
            lc = observed[source]
            abstract[name(source)] = {'kind':'constant','value':lc[0][1] if lc else 0}
            derived[source] = lc
            continue
        multiply,left,right = nodes[source]
        abstract[name(source)] = {'kind':'mul' if multiply else 'add','left':name(left),'right':name(right)}
        folded = None
        if multiply:
            for const,other in ((derived[left],derived[right]),(derived[right],derived[left])):
                if all(c == 0 for c,_ in const):
                    factor = const[0][1] if const else 0
                    folded = canonical((c,v*factor) for c,v in other)
                    break
            if folded is None:
                if source not in observed: raise relation.RelationError('missing RNK nonlinear output LC')
                folded = observed[source]
        else: folded = canonical(derived[left]+derived[right])
        derived[source] = folded
        if source in observed and observed[source] != folded:
            raise relation.RelationError('RNK source arithmetic/compiler LC mismatch')
    width = len(before)
    params = poseidon_graph.parameters(parameter_root/('poseidon381-wide.json' if width == 6 else 'poseidon381.json'),width)
    graph = poseidon_graph.permutation(params,[int(x['native'],16) if 'native' in x else None for x in before])
    try:
        pairs = poseidon_graph.match_permutation(graph,abstract,[names[x] for x in boundaries],[name(x) for x in outputs])
    except ValueError as error:
        raise relation.RelationError('RNK permutation source mismatch: '+str(error)) from error
    if {actual for _,actual in pairs} != set(abstract):
        raise relation.RelationError('unmatched RNK permutation source cone')
    checked.update(nodes=nodes,derived=derived,graph=graph,pairs=pairs,source=abstract,
                   source_names={x:name(x) for x in visited},inputs=boundaries,outputs=outputs,
                   metadata_sha256=hashlib.sha256(data).hexdigest(),
                   scope='closed permutation DAG/all-lane LC consistency only; actual rows and kernel proof open')
    return checked


def extract(data, stream, parameter_root, expected_relation, ivk_handles, expected_rnk_bindings):
    """Require exact ordinary square/product rows for every nonlinear node."""
    checked = inspect_metadata(data,parameter_root,expected_relation,ivk_handles,expected_rnk_bindings)
    copy = checked['metadata']['constant_copy']
    def outline(lc): return canonical((copy if c == 0 else c,v) for c,v in lc)
    def negate(lc): return canonical((c,-v) for c,v in lc)
    required = {(canonical([(0,1),(copy,P-1)]),()):['constant-copy']}
    products = []
    for node,(multiply,left,right) in checked['nodes'].items():
        if not multiply: continue
        a,b,z = (checked['derived'][x] for x in (left,right,node))
        if any(all(c == 0 for c,_ in lc) for lc in (a,b)): continue
        role = 'node.'+str(node[1])
        if a == b:
            required.setdefault((outline(a),outline(z)),[]).append(role)
        else:
            products.append((role,outline(canonical(a+negate(b))),outline(canonical(a+b)),outline(z)))
    targets = {lc for _,minus,plus,_ in products for lc in (minus,negate(minus),plus)}
    matched,candidates,rows = {},{},{}
    def observe(row):
        a,b = (tuple((c,int(v,16)) for c,v in row[k]) for k in ('a','b'))
        key = (a,b) if (a,b) in required else (negate(a),b)
        if key in required:
            matched.setdefault(key,row['row']); rows[row['row']] = row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row['row'])); rows[row['row']] = row
            if len(candidates[a]) > 128:
                raise relation.RelationError('RNK product candidate bound exceeded')
        if len(rows) > 8192:
            raise relation.RelationError('RNK physical row selection exceeds finite bound')
    identity = relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if (identity['domain_size'] != checked['metadata']['domain_size']
            or identity['stored_rows'] != checked['metadata']['full_rows']):
        raise relation.RelationError('RNK hash ordinary relation shape mismatch')
    missing = set(required)-set(matched)
    if missing: raise relation.RelationError('missing actual RNK square/copy row')
    pairs = []
    for role,minus,plus,z in products:
        pair = next(((i,j) for aux,i in candidates.get(minus,[])+candidates.get(negate(minus),[])
                     for b,j in candidates.get(plus,[]) if b == canonical(aux+tuple((c,4*v) for c,v in z))),None)
        if pair is None: raise relation.RelationError('missing actual RNK product '+role)
        pairs.append({'role':role,'rows':list(pair)})
    indices = set(matched.values()) | {i for p in pairs for i in p['rows']}
    return {'identity':identity,'metadata_sha256':checked['metadata_sha256'],'block':checked['block'],
            'templates':[{'roles':roles,'row':matched[key]} for key,roles in required.items()],
            'products':pairs,'selected_rows':[rows[i] for i in sorted(indices)],
            'scope':'actual permutation row extraction only; kernel and sponge/source interpretation joins open'}


def round_selection(data, extracted, parameter_root, expected_relation, ivk_handles, expected_rnk_bindings):
    """Build the existing round-certificate interface without inventing absorption."""
    checked = inspect_metadata(data,parameter_root,expected_relation,ivk_handles,expected_rnk_bindings)
    if extracted.get('metadata_sha256') != checked['metadata_sha256'] or extracted.get('block') != checked['block']:
        raise relation.RelationError('RNK round extraction metadata mismatch')
    identity = extracted.get('identity',{})
    if (identity.get('relation_digest') != expected_relation
            or identity.get('domain_size') != checked['metadata']['domain_size']
            or identity.get('stored_rows') != checked['metadata']['full_rows']):
        raise relation.RelationError('RNK round extraction relation mismatch')
    copy = checked['metadata']['constant_copy']
    raw = {}
    for row in extracted['selected_rows']:
        if not isinstance(row,dict) or set(row) != {'row','a','b'}:
            raise relation.RelationError('malformed RNK selected row')
        index = relation.natural(row['row'],identity['stored_rows'])
        if index in raw: raise relation.RelationError('duplicate RNK selected row')
        for k in ('a','b'): relation.terms(row[k],identity['domain_size'])
        raw[index] = tuple(tuple((c,int(v,16)) for c,v in row[k]) for k in ('a','b'))
    table,squared = {},{}
    for index,(a,b) in sorted(raw.items()):
        a,b = (canonical((0 if c == copy else c,v) for c,v in lc) for lc in (a,b))
        table.setdefault((a,b),index); squared.setdefault(a,[]).append((b,index))
    link = (canonical([(0,1),(copy,P-1)]),())
    links = [i for i,pair in raw.items() if pair == link]
    if len(links) != 1: raise relation.RelationError('missing/ambiguous RNK round constant copy')
    observations = {checked['source_names'][x]:lc for x,lc in checked['derived'].items()}
    matches = {}
    for expected,actual in checked['pairs']: matches.setdefault(expected,set()).add(actual)
    graph,cache = checked['graph'],{}
    def terms(index):
        if index in cache: return cache[index]
        node = graph['nodes'][index]
        if index in matches:
            values = {observations[x] for x in matches[index]}
            if len(values) != 1: raise relation.RelationError('unequal shared RNK graph LC')
            lc = next(iter(values))
        elif node['kind'] == 'constant': lc = canonical([(0,node['value'])])
        else: raise relation.RelationError('unmatched RNK round graph node')
        cache[index] = lc
        return lc
    segments = []
    for segment in graph['segments']:
        fifths,rows = {},set()
        for lane,power in segment['powers'].items():
            base = terms(segment['shifted'][lane])
            transformed = terms(segment['transformed'][lane])
            if all(c == 0 for c,_ in base):
                coefficient = base[0][1] if base else 0
                if transformed != canonical([(0,pow(coefficient,5,P))]):
                    raise relation.RelationError('RNK constant fifth mismatch')
                fifths[lane] = {'kind':'constant','coefficient':coefficient}
                continue
            square,fourth = terms(power['square']),terms(power['fourth'])
            if (base,square) not in table or (square,fourth) not in table:
                raise relation.RelationError('missing exact RNK fifth square')
            minus = canonical(fourth+tuple((c,-v) for c,v in base)); plus = canonical(fourth+base)
            candidates = [(i,table[(plus,canonical(aux+tuple((c,4*v) for c,v in transformed)))],aux)
                          for aux,i in squared.get(minus,[])
                          if (plus,canonical(aux+tuple((c,4*v) for c,v in transformed))) in table]
            if not candidates: raise relation.RelationError('missing exact oriented RNK fifth product')
            i,j,aux = min(candidates)
            indices = [table[(base,square)],table[(square,fourth)],i,j]
            rows.update(indices)
            fifths[lane] = dict(kind='arithmetic',square=square,fourth=fourth,auxiliary=aux,rows=indices)
        segments.append(dict(kind='round',chunk=0,index=segment['round'],
                             before=[terms(i) for i in segment['before']],shifted=[terms(i) for i in segment['shifted']],
                             transformed=[terms(i) for i in segment['transformed']],after=[terms(i) for i in segment['after']],
                             fifths=fifths,rows=sorted(rows)))
    width = graph['width']
    params = poseidon_graph.parameters(parameter_root/('poseidon381-wide.json' if width == 6 else 'poseidon381.json'),width)
    role = 'authorization.rnk_permutation'+str(checked['block'])
    call = dict(graph={**graph,'domain':17 if checked['block'] < 2 else 18},
                inputs=[checked['source_names'][x] for x in checked['inputs']],
                output=checked['source_names'][checked['outputs'][1]])
    return {'outline':copy,'constant_link':links[0],'rows':raw,
            'calls':[dict(role=role,segments=segments,parameters=params,call=call)],
            'observations':{name:('linear',lc) for name,lc in observations.items()},
            'scope':'one actual permutation round selection; no absorption/hash theorem'}


def ingress_controls(data, parameter_root, expected_relation, ivk_handles, expected_rnk_bindings):
    """Observe specific parser refusals; these are not underconstraint controls."""
    state = inspect_metadata(data,parameter_root,expected_relation,ivk_handles,expected_rnk_bindings)
    original = state['metadata']
    mutations = []
    def add(name,reason,change):
        obj = copy.deepcopy(original); change(obj); mutations.append((name,reason,obj))
    add('wrong-domain','wrong RNK hash domain/arity/blocks',lambda o:o['hashes'][0].update(domain=18))
    add('wrong-caller','RNK hash/accepted caller role mismatch',
        lambda o:o['rnk_bindings'].update(regulated=o['rnk_bindings']['registered']))
    add('missing-source-node','missing RNK permutation node',lambda o:o['nodes'].pop())
    add('capacity-transition','RNK wide absorption LC mismatch',
        lambda o:o['hashes'][0]['blocks'][1]['before'].__setitem__(0,o['hashes'][0]['blocks'][0]['after'][1]))
    # Leave output lane1 intact; change another output in the selected block.
    call,block = (0,state['block']) if state['block'] < 2 else (1,0)
    def nonoutput_lane(obj):
        changed = obj['hashes'][call]['blocks'][block]['after'][1]
        obj['hashes'][call]['blocks'][block]['after'][0] = changed
        if state['block'] == 0:
            obj['hashes'][0]['blocks'][1]['before'][0] = changed
    add('nonoutput-lane','extra RNK permutation nodes',nonoutput_lane)
    results = []
    for name,reason,obj in mutations:
        try:
            inspect_metadata((json.dumps(obj,separators=(',',':'))+'\n').encode(),parameter_root,
                             expected_relation,ivk_handles,expected_rnk_bindings)
        except relation.RelationError as error:
            if reason not in str(error):
                raise relation.RelationError('unrelated RNK ingress refusal '+name+': '+str(error)) from error
            results.append(dict(name=name,rejection=str(error)))
        else: raise relation.RelationError('RNK ingress mutation accepted '+name)
    return {'metadata_sha256':state['metadata_sha256'],'controls':results,
            'scope':'structural ingress/source controls only; no semantic row omission claim'}


def extract_selection(data, stream, expected_relation, ivk_handles, expected_rnk_bindings):
    """Select the actual regulated commitment gate and effective-NK product."""
    state = inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    obj,observed = state['metadata'],state['observed']
    copy_column = obj['constant_copy']
    def lc(ref):
        if not isinstance(ref,dict) or set(ref) != {'source'}:
            raise relation.RelationError('RNK selection requires captured Source roles')
        return observed[source_index(ref['source'])]
    def outline(terms): return canonical((copy_column if c == 0 else c,v) for c,v in terms)
    def neg(terms): return canonical((c,-v) for c,v in terms)
    bindings = obj['rnk_bindings']
    reg,nk = lc(bindings['regulated']),observed[tuple(ivk_handles[0])]
    commit,registered,rnk,effective = (lc(bindings[k]) for k in ('commitment','registered','hash','effective_nk'))
    gate_delta = canonical(commit+neg(registered))
    selector_delta = canonical(rnk+neg(nk))
    output = canonical(effective+neg(nk))
    gate_minus,gate_plus = outline(canonical(reg+neg(gate_delta))),outline(canonical(reg+gate_delta))
    select_minus,select_plus = outline(canonical(reg+neg(selector_delta))),outline(canonical(reg+selector_delta))
    targets = {gate_minus,neg(gate_minus),gate_plus,select_minus,neg(select_minus),select_plus}
    boolean,copy = (outline(reg),outline(reg)),(canonical([(0,1),(copy_column,P-1)]),())
    candidates,matched,gate_assertions = {},{},{}
    gate_outputs = set()
    def observe(row):
        a,b = (tuple((c,int(v,16)) for c,v in row[k]) for k in ('a','b'))
        if (a,b) in (boolean,copy): matched[(a,b)] = row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row))
            if len(candidates[a]) > 128: raise relation.RelationError('RNK selection candidate bound exceeded')
            for aux,_ in candidates.get(gate_minus,[])+candidates.get(neg(gate_minus),[]):
                for plus_b,_ in candidates.get(gate_plus,[]):
                    gate_outputs.add(canonical((c,v*pow(4,-1,P)) for c,v in canonical(plus_b+neg(aux))))
        if not b:
            for candidate in gate_outputs:
                if a in (candidate,neg(candidate)): gate_assertions[candidate] = row
    identity = relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size'] != obj['domain_size'] or identity['stored_rows'] != obj['full_rows']:
        raise relation.RelationError('RNK selection ordinary relation shape mismatch')
    if boolean not in matched or copy not in matched:
        raise relation.RelationError('missing RNK selection Boolean/copy row')
    selector = next(((minus,plus) for aux,minus in candidates.get(select_minus,[])+candidates.get(neg(select_minus),[])
                     for b,plus in candidates.get(select_plus,[])
                     if b == canonical(aux+tuple((c,4*v) for c,v in outline(output)))),None)
    gate = next(((minus,plus,gate_assertions[z],z)
                 for aux,minus in candidates.get(gate_minus,[])+candidates.get(neg(gate_minus),[])
                 for b,plus in candidates.get(gate_plus,[])
                 for z in [canonical((c,v*pow(4,-1,P)) for c,v in canonical(b+neg(aux)))]
                 if z in gate_assertions),None)
    if selector is None or gate is None:
        raise relation.RelationError('missing actual RNK selection product/gate assertion')
    rows = {row['row']:row for row in [matched[boolean],matched[copy],*selector,*gate[:3]]}
    return {'identity':identity,'metadata_sha256':hashlib.sha256(data).hexdigest(),
            'roles':{'boolean':matched[boolean]['row'],'copy':matched[copy]['row'],
                     'selector':[row['row'] for row in selector],'gate':[row['row'] for row in gate[:3]]},
            'selected_rows':[rows[i] for i in sorted(rows)],
            'gate_output':[[c,f'{v:064x}'] for c,v in gate[3]],
            'scope':'actual regulated gate/effective-NK rows only; hash/branch kernel and full Transfer joins open'}


def extract_ring_selection(data, stream, expected_relation, ivk_handles, expected_rnk_bindings,
                           *, leaf_columns, fixed_coordinates, inverse_column):
    """Check candidate ring coordinates against actual rows, not caller role names.

    The fixed point's native derivation and the leaf's caller role remain separate.
    """
    state = inspect_boundaries(data, expected_relation, ivk_handles, expected_rnk_bindings)
    obj, observed = state['metadata'], state['observed']
    if (not isinstance(leaf_columns,(list,tuple)) or len(leaf_columns) != 2 or
            not isinstance(fixed_coordinates,(list,tuple)) or len(fixed_coordinates) != 2):
        raise relation.RelationError('wrong selected-ring candidate shape')
    columns = [relation.natural(c,obj['domain_size']) for c in [*leaf_columns,inverse_column]]
    if len(set(columns)) != 3 or any(c in (0,obj['constant_copy']) for c in columns):
        raise relation.RelationError('invalid selected-ring candidate columns')
    if any(isinstance(x,bool) or not isinstance(x,int) or not 0 <= x < P for x in fixed_coordinates):
        raise relation.RelationError('noncanonical selected-ring fixed coordinate')
    def lc(ref):
        if not isinstance(ref,dict) or set(ref) != {'source'}:
            raise relation.RelationError('selected-ring boundary requires Source')
        return observed[source_index(ref['source'])]
    bindings = obj['rnk_bindings']
    regulated = lc(bindings['regulated'])
    selected = [lc(ref) for ref in bindings['inputs'][7:9]]
    fixed = [canonical([(0,x)]) for x in fixed_coordinates]
    leaf = [canonical([(c,1)]) for c in leaf_columns]
    inverse = canonical([(inverse_column,1)])
    def neg(x): return canonical((c,-v) for c,v in x)
    def outline(x): return canonical((obj['constant_copy'] if c == 0 else c,v) for c,v in x)
    products = [(regulated,canonical(a+neg(b)),canonical(s+neg(b)))
                for a,b,s in zip(leaf,fixed,selected)]
    products.append((inverse,selected[0],None))
    targets = set()
    for a,b,_ in products:
        minus,plus = outline(canonical(a+neg(b))),outline(canonical(a+b))
        targets.update((minus,neg(minus),plus))
    candidates, assertions, exact = {},{},{}
    inverse_assertions = set()
    boolean = (outline(regulated),outline(regulated))
    copy = (canonical([(0,1),(obj['constant_copy'],P-1)]),())
    def observe(row):
        a,b = (tuple((c,int(v,16)) for c,v in row[k]) for k in ('a','b'))
        if (a,b) in (boolean,copy): exact[(a,b)] = row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row))
            if len(candidates[a]) > 128:
                raise relation.RelationError('selected-ring product candidate bound')
            inverse_minus=outline(canonical(inverse+neg(selected[0])))
            inverse_plus=outline(canonical(inverse+selected[0]))
            for aux,_ in candidates.get(inverse_minus,[])+candidates.get(neg(inverse_minus),[]):
                for plus_b,_ in candidates.get(inverse_plus,[]):
                    output=canonical((c,v*pow(4,-1,P)) for c,v in canonical(plus_b+neg(aux)))
                    delta=canonical(output+((obj['constant_copy'],P-1),))
                    inverse_assertions.update((delta,neg(delta)))
        if not b and a in inverse_assertions:
            assertions.setdefault(a,[]).append(row)
            if len(assertions[a]) > 128:
                raise relation.RelationError('selected-ring assertion candidate bound')
    identity = relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size'] != obj['domain_size'] or identity['stored_rows'] != obj['full_rows']:
        raise relation.RelationError('selected-ring ordinary shape mismatch')
    if boolean not in exact or copy not in exact:
        raise relation.RelationError('missing selected-ring Boolean/copy row')
    matched=[]
    for a,b,output in products:
        minus,plus = outline(canonical(a+neg(b))),outline(canonical(a+b))
        choices=[]
        for aux,minus_row in candidates.get(minus,[])+candidates.get(neg(minus),[]):
            for plus_b,plus_row in candidates.get(plus,[]):
                actual = canonical((c,v*pow(4,-1,P)) for c,v in canonical(plus_b+neg(aux)))
                if output is not None:
                    if actual == outline(output): choices.append((minus_row,plus_row,None,actual))
                else:
                    delta=canonical(actual+((obj['constant_copy'],P-1),))
                    for assertion in assertions.get(delta,[])+assertions.get(neg(delta),[]):
                        choices.append((minus_row,plus_row,assertion,actual))
        if len(choices) != 1:
            raise relation.RelationError('missing/ambiguous selected-ring product or inverse assertion')
        matched.append(choices[0])
    rows={r['row']:r for r in [exact[boolean],exact[copy]]}
    for choice in matched:
        for r in choice[:3]:
            if r is not None: rows[r['row']]=r
    return dict(identity=identity,metadata_sha256=hashlib.sha256(data).hexdigest(),
                leaf_columns=list(leaf_columns),fixed_coordinates=list(fixed_coordinates),
                inverse_column=inverse_column,
                roles=dict(boolean=exact[boolean]['row'],copy=exact[copy]['row'],
                           products=[[r['row'] for r in choice[:3] if r is not None] for choice in matched]),
                selected_rows=[rows[i] for i in sorted(rows)],
                scope='actual selected-ring coordinate/Boolean/inverse rows; caller leaf and native fixed-point joins open')


def generate_ring_selection(data, extracted, expected_relation, ivk_handles, expected_rnk_bindings):
    """Actual selector equations; candidate leaf and native fixed-point roles stay open."""
    from .generate_hash_round import linear, _signature_audits
    state=inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    identity=extracted.get('identity',{})
    if (extracted.get('metadata_sha256') != hashlib.sha256(data).hexdigest() or
            identity.get('relation_digest') != expected_relation or
            identity.get('domain_size') != state['metadata']['domain_size'] or
            identity.get('stored_rows') != state['metadata']['full_rows']):
        raise relation.RelationError('selected-ring extraction identity mismatch')
    rows={}
    for row in extracted['selected_rows']:
        if not isinstance(row,dict) or set(row) != {'row','a','b'}:
            raise relation.RelationError('malformed selected-ring row')
        i=relation.natural(row['row'],identity['stored_rows'])
        if i in rows: raise relation.RelationError('duplicate selected-ring row')
        for key in ('a','b'): relation.terms(row[key],identity['domain_size'])
        rows[i]=row
    roles=extracted['roles']
    if (set(roles) != {'boolean','copy','products'} or len(rows) != 9 or
            list(map(len,roles['products'])) != [2,2,3] or
            set(rows) != {roles['boolean'],roles['copy'],*(i for pair in roles['products'] for i in pair)}):
        raise relation.RelationError('wrong selected-ring row inventory')
    def parse(terms):return tuple((c,int(v,16)) for c,v in terms)
    def lc(ref):return state['observed'][source_index(ref['source'])]
    bindings=state['metadata']['rnk_bindings']
    values={'regulated':lc(bindings['regulated']),
            'inverse':canonical([(extracted['inverse_column'],1)]),
            'inverseOutput':canonical((c,v*pow(4,-1,P)) for c,v in canonical(
                parse(rows[roles['products'][2][1]]['b'])+
                tuple((c,-v) for c,v in parse(rows[roles['products'][2][0]]['b'])))),
            'inverseAux':parse(rows[roles['products'][2][0]]['b'])}
    for axis,index in (('x',0),('y',1)):
        values['selected'+axis]=lc(bindings['inputs'][7+index])
        values['fixed'+axis]=canonical([(0,extracted['fixed_coordinates'][index])])
        values['leaf'+axis]=canonical([(extracted['leaf_columns'][index],1)])
        values['output'+axis]=canonical(values['selected'+axis]+tuple((c,-v) for c,v in values['fixed'+axis]))
        values['aux'+axis]=parse(rows[roles['products'][index][0]]['b'])
    source=f'''import ShielddSecurity.ScalarComparisonBounds
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeRnkRingSelection
-- Actual ordinary relation: {expected_relation}
-- Candidate leaf roles and native fixed-point interpretation remain open.
def modulus : Nat := {P}
def rawRows : List Row := [
'''+',\n'.join('  ⟨'+linear(parse(rows[i]['a']))+', '+linear(parse(rows[i]['b']))+'⟩' for i in sorted(rows))+']\n'
    source+=''.join(f'def {name} : Linear := {linear(value)}\n' for name,value in values.items())
    source+='''
theorem regulated_boolean {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho regulated = 0 ∨ eval rho regulated = 1 := by
  apply boolean_sound
  exact Compiler.checked_row_sound rho rawRows ⟨regulated,regulated⟩ satisfied (by decide)
'''
    for axis in ('x','y'):
        source+=f'''
theorem selected_{axis}_equation {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho selected{axis} = eval rho fixed{axis} +
      eval rho regulated * (eval rho leaf{axis} - eval rho fixed{axis}) := by
  have product := Compiler.checked_product_sound rho rawRows regulated
    (Compiler.subtract leaf{axis} fixed{axis}) output{axis} aux{axis} four satisfied (by decide) (by decide)
  have difference := Compiler.canonical_equal rho output{axis} (Compiler.subtract selected{axis} fixed{axis}) (by decide)
  rw [Compiler.eval_subtract] at product difference
  rw [difference] at product
  exact (sub_eq_iff_eq_add.mp product).trans (by ring)
'''
    source+='''
theorem selected_x_nonzero {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho selectedx ≠ 0 := by
  have product := Compiler.checked_product_sound rho rawRows inverse selectedx
    inverseOutput inverseAux four satisfied (by decide) (by decide)
  have asserted := ScalarComparisonBounds.checked_equality rho rawRows satisfied
    inverseOutput [(200692,1)] (by decide)
  have copied := ScalarComparisonBounds.checked_equality rho rawRows satisfied
    [(0,1)] [(200692,1)] (by decide)
  have equation : eval rho inverse * eval rho selectedx = 1 :=
    product.symm.trans (asserted.trans (copied.symm.trans (by simp [eval,one])))
  intro zero
  rw [zero,mul_zero] at equation
  exact zero_ne_one equation
#print axioms regulated_boolean
#print axioms selected_x_equation
#print axioms selected_y_equation
#print axioms selected_x_nonzero
end ShielddSecurity.RuntimeRnkRingSelection
'''
    copy=state['metadata']['constant_copy']
    source=source.replace('theorem regulated_boolean', f'''def rows : List Row := Compiler.unoutlineRows {copy} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide

theorem regulated_boolean''',1)
    normalized=f'''  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
'''
    source=source.replace('  have product :=',normalized+'  have product :=')
    source=source.replace('Compiler.checked_product_sound rho rawRows','Compiler.checked_product_sound rho rows')
    source=source.replace('four satisfied (by decide) (by decide)','four normalized (by decide) (by decide)')
    source=source.replace('ScalarComparisonBounds.checked_equality rho rawRows satisfied\n    inverseOutput [(200692,1)]',
                          'ScalarComparisonBounds.checked_equality rho rows normalized\n    inverseOutput [(0,1)]')
    source=source.replace('  have copied := ScalarComparisonBounds.checked_equality rho rawRows satisfied\n    [(0,1)] [(200692,1)] (by decide)\n','')
    source=source.replace('product.symm.trans (asserted.trans (copied.symm.trans (by simp [eval,one])))',
                          'product.symm.trans (asserted.trans (by simp [eval,one]))')
    source=source.replace('#print axioms regulated_boolean','#print axioms constantLink\n#print axioms regulated_boolean')
    return _signature_audits(source)


def generate_ring_subgroup_join():
    """Join registry subgroup rows to actual ring selection; fixed native role stays open."""
    from .generate_hash_round import _signature_audits
    source='''import ShielddSecurity.RuntimeRegistryRing
import ShielddSecurity.RuntimeRnkRingSelection
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeSelectedRing
def modulus : Nat := RuntimeRegistryRing.modulus
def rawRows : List Row := RuntimeRegistryRing.rawRows ++ RuntimeRnkRingSelection.rawRows
def selected {F : Type} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho RuntimeRnkRingSelection.selectedx,eval rho RuntimeRnkRingSelection.selectedy⟩
def fixed {F : Type} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho RuntimeRnkRingSelection.fixedx,eval rho RuntimeRnkRingSelection.fixedy⟩

theorem leaf_columns {F : Type} [Field F] (rho : Nat → F) :
    RuntimeRegistryRing.point rho =
      Group.Point.mk (eval rho RuntimeRnkRingSelection.leafx)
        (eval rho RuntimeRnkRingSelection.leafy) := rfl

theorem actual_selected_ring {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (model : Group.StandardCurveModel J (RuntimeTransferCofactorCones.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferCofactor.subgroupOrder) • represented = 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ leaf : J, model.coordinates leaf = RuntimeRegistryRing.point rho ∧
      RuntimeTransferCofactor.subgroupOrder • leaf = 0 ∧
      (selected rho).x ≠ 0 ∧
      ((eval rho RuntimeRnkRingSelection.regulated = 0 ∧ selected rho = fixed rho) ∨
       (eval rho RuntimeRnkRingSelection.regulated = 1 ∧ selected rho = model.coordinates leaf)) := by
  have leafSat : Satisfies rho RuntimeRegistryRing.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have selectedSat : Satisfies rho RuntimeRnkRingSelection.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  obtain ⟨leaf,coordinates,subgroup⟩ := RuntimeRegistryRing.actual_subgroup model standardOrder rho one leafSat
  have x := RuntimeRnkRingSelection.selected_x_equation rho four selectedSat
  have y := RuntimeRnkRingSelection.selected_y_equation rho four selectedSat
  have nonzero := RuntimeRnkRingSelection.selected_x_nonzero rho one four selectedSat
  refine ⟨leaf,coordinates,subgroup,nonzero,?_⟩
  rcases RuntimeRnkRingSelection.regulated_boolean rho selectedSat with unregulated | regulated
  · left
    refine ⟨unregulated,?_⟩
    apply congrArg₂ Group.Point.mk
    · simpa only [unregulated,zero_mul,add_zero] using x
    · simpa only [unregulated,zero_mul,add_zero] using y
  · right
    refine ⟨regulated,?_⟩
    rw [coordinates,leaf_columns rho]
    apply congrArg₂ Group.Point.mk
    · rw [regulated,one_mul] at x
      exact x.trans (by ring)
    · rw [regulated,one_mul] at y
      exact y.trans (by ring)
#print axioms leaf_columns
#print axioms actual_selected_ring
end ShielddSecurity.RuntimeSelectedRing
'''
    return _signature_audits(source)


def generate_fixed_ring_cofactor():
    """Finite polynomial certificate for the captured constants, not their native derivation."""
    from .generate_hash_round import _signature_audits
    d=-10240*pow(10241,-1,P)%P
    points=[
      (21289474763898676139701362251463913461252610982741592724099370957156748763823,
       8265138916156413747133500806512861797220164717963959335892920993251552451726),
      (24144365962855066261376867565841756026821714715142989725940173278472340279724,
       35085498316710194104910971298504693676956536634943856485443562968667694889799),
      (12741252908976003547701397644694341362306543933702396285100647387649400890335,
       4446312979066948445530332005038299922818903706706908173311402749816250395214),
      (49822839976625491399435002605169580882773999909559575334089637637825427273330,
       29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    source=f'''import ShielddSecurity.TransferSubgroup
import ShielddSecurity.RuntimeTransferCofactorCones
set_option maxHeartbeats 800000
namespace ShielddSecurity.RuntimeFixedRing
-- Exact captured constant coordinates only; native domain29/map construction remains open.
def modulus : Nat := {P}
def coefficientD : Int := {d}
'''
    for i,(x,y) in enumerate(points):
        source+=f'def point{i} {{F : Type}} [Field F] : Group.Point F := ⟨(({x} : Int) : F),(({y} : Int) : F)⟩\n'
    source+='''
private theorem constant_zero {F : Type} [Field F] [CharP F modulus]
    (value : Int) (checked : value % (modulus : Int) = 0) : (value : F) = 0 := by
  have reduced := Compiler.coefficient_mod (F := F) (p := modulus) value
  rw [checked] at reduced
  simpa only [Int.cast_zero] using reduced.symm

theorem coefficient_matches : coefficientD = RuntimeTransferCofactorCones.coefficientD := by decide
'''
    def certify(name,field_expression,integer_expression):
        return f'''  have {name} : {field_expression} = 0 := by
    have checked := constant_zero (F := F) ({integer_expression} : Int) (by decide)
    convert checked using 1 <;> simp only [coefficientD,point0,point1,point2,point3,
      Group.cross,Group.diagonal,Group.delta,Int.cast_add,Int.cast_sub,Int.cast_mul,
      Int.cast_one,Int.cast_zero] <;> ring
'''
    x,y=points[0]
    source+='''
theorem preimage_oncurve {F : Type} [Field F] [CharP F modulus] :
    Group.OnCurve (coefficientD : F) (point0 : Group.Point F) := by
'''
    source+=certify('checked', '(point0 : Group.Point F).y * point0.y - point0.x * point0.x - (1 + (coefficientD : F) * point0.x * point0.x * point0.y * point0.y)',
                   f'{y}*{y}-{x}*{x}-1-{d}*{x}*{x}*{y}*{y}')
    source+='  exact sub_eq_zero.mp checked\n'
    for i in range(3):
        x,y=points[i]; u,v=points[i+1]; delta=d*x*x*y*y
        inv=pow((1-delta*delta)%P,-1,P)
        delta_expression=f'{d}*{x}*{x}*{y}*{y}'
        source+=f'''
theorem double{i} {{F : Type}} [Field F] [CharP F modulus] :
    (point{i+1} : Group.Point F) = Group.affineAdd (coefficientD : F) point{i} point{i} := by
'''
        source+=certify('inverse',f'((1 + Group.delta (coefficientD : F) point{i} point{i}) * (1 - Group.delta (coefficientD : F) point{i} point{i})) * (({inv} : Int) : F) - 1',
                       f'(1+({delta_expression}))*(1-({delta_expression}))*{inv}-1')
        source+=certify('xEquation',f'(point{i+1} : Group.Point F).x - Group.cross point{i} point{i} * (1 - Group.delta (coefficientD : F) point{i} point{i}) * (({inv} : Int) : F)',
                       f'{u}-({x}*{y}+{x}*{y})*(1-({delta_expression}))*{inv}')
        source+=certify('yEquation',f'(point{i+1} : Group.Point F).y - Group.diagonal point{i} point{i} * (1 + Group.delta (coefficientD : F) point{i} point{i}) * (({inv} : Int) : F)',
                       f'{v}-({y}*{y}+{x}*{x})*(1+({delta_expression}))*{inv}')
        source+=f'''  exact TransferSubgroup.shared_inverse_affine (coefficientD : F) (({inv} : Int) : F)
    point{i} point{i} point{i+1} (sub_eq_zero.mp inverse)
    (sub_eq_zero.mp xEquation) (sub_eq_zero.mp yEquation)
'''
    source+='''
theorem fixed_subgroup {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (model : Group.StandardCurveModel J (coefficientD : F))
    (order : Nat) (standardOrder : ∀ represented : J, (8 * order) • represented = 0) :
    ∃ represented : J, model.coordinates represented = (point3 : Group.Point F) ∧ order • represented = 0 := by
  exact Group.cofactor_image_annihilated (coefficientD : F) model order standardOrder
    point0 point1 point2 point3 preimage_oncurve double0 double1 double2
#print axioms coefficient_matches
#print axioms preimage_oncurve
#print axioms double0
#print axioms double1
#print axioms double2
#print axioms fixed_subgroup
end ShielddSecurity.RuntimeFixedRing
'''
    return _signature_audits(source)


def generate_selected_ring_subgroup():
    """Derive the selected subgroup point, without native or caller-role assumptions."""
    from .generate_hash_round import _signature_audits
    source='''import ShielddSecurity.RuntimeSelectedRing
import ShielddSecurity.RuntimeFixedRing
import ShielddSecurity.RuntimeRnkSponge
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeSelectedRingSubgroup
def modulus : Nat := RuntimeSelectedRing.modulus
def rawRows : List Row := RuntimeSelectedRing.rawRows

theorem fixed_coordinates {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    RuntimeSelectedRing.fixed rho = (RuntimeFixedRing.point3 : Group.Point F) := by
  apply congrArg₂ Group.Point.mk
  · have same := Compiler.canonical_equal rho RuntimeRnkRingSelection.fixedx
      [(0,49822839976625491399435002605169580882773999909559575334089637637825427273330)]
      (p := modulus) (by decide)
    exact same.trans (by simp [eval,one])
  · have same := Compiler.canonical_equal rho RuntimeRnkRingSelection.fixedy
      [(0,29108985603249989484651727880329493522712908252517904247459350893053326313050)]
      (p := modulus) (by decide)
    exact same.trans (by simp [eval,one])

theorem hash_ring_input_values {F : Type} [Field F] (rho : Nat → F) :
    (RuntimeRnkSponge.inputs.drop 7).map (eval rho) =
      [(RuntimeSelectedRing.selected rho).x,(RuntimeSelectedRing.selected rho).y] := rfl

theorem actual_selected_subgroup {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (model : Group.StandardCurveModel J (RuntimeTransferCofactorCones.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferCofactor.subgroupOrder) • represented = 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ represented : J, model.coordinates represented = RuntimeSelectedRing.selected rho ∧
      RuntimeTransferCofactor.subgroupOrder • represented = 0 ∧ represented ≠ 0 := by
  obtain ⟨leaf,leafRole,leafSubgroup,nonzero,branches⟩ :=
    RuntimeSelectedRing.actual_selected_ring rho one four model standardOrder satisfied
  let fixedModel : Group.StandardCurveModel J (RuntimeFixedRing.coefficientD : F) := model
  obtain ⟨constant,constantRole,constantSubgroup⟩ := RuntimeFixedRing.fixed_subgroup
    fixedModel RuntimeTransferCofactor.subgroupOrder standardOrder
  have constantCoordinates : model.coordinates constant = RuntimeSelectedRing.fixed rho := by
    exact constantRole.trans (fixed_coordinates rho one).symm
  rcases branches with ⟨unregulated,selectedFixed⟩ | ⟨regulated,selectedLeaf⟩
  · have coordinates := constantCoordinates.trans selectedFixed.symm
    refine ⟨constant,coordinates,constantSubgroup,?_⟩
    apply Group.represented_nonidentity _ model constant
    rw [coordinates]
    exact nonzero
  · refine ⟨leaf,selectedLeaf.symm,leafSubgroup,?_⟩
    apply Group.represented_nonidentity _ model leaf
    rw [← selectedLeaf]
    exact nonzero
#print axioms fixed_coordinates
#print axioms hash_ring_input_values
#print axioms actual_selected_subgroup
end ShielddSecurity.RuntimeSelectedRingSubgroup
'''
    return _signature_audits(source)


def generate_rnk_points_join():
    """Bind both proved group points into the RNK hash at one assignment."""
    from .generate_hash_round import _signature_audits
    previous=generate_dh_sponge_join()
    signature=previous.split('theorem actual_ivk_dh_hash',1)[1].split(' := by',1)[0]
    signature=signature.replace('∃ senderBase : J,','∃ senderBase selectedRing : J,')
    signature=signature.replace('((RuntimeRnkSponge.inputs.drop 2).map (eval rho))',
        '(middleInputs.map (eval rho) ++ [(model.coordinates selectedRing).x,(model.coordinates selectedRing).y])')
    source='''import ShielddSecurity.RuntimeRnkJoined
import ShielddSecurity.RuntimeSelectedRingSubgroup
set_option maxHeartbeats 800000
namespace ShielddSecurity.RuntimeRnkPoints
def modulus : Nat := RuntimeRnkJoined.modulus
def rawRows : List Row := RuntimeRnkJoined.rawRows ++ RuntimeSelectedRingSubgroup.rawRows
def middleInputs : List Linear := (RuntimeRnkSponge.inputs.drop 2).take 5

theorem selected_input_values {F : Type} [Field F] (rho : Nat → F) :
    (RuntimeRnkSponge.inputs.drop 2).map (eval rho) =
      middleInputs.map (eval rho) ++
        [(RuntimeSelectedRing.selected rho).x,(RuntimeSelectedRing.selected rho).y] := rfl

theorem actual_rnk_points''' + signature + ''' ∧
      model.coordinates selectedRing = RuntimeSelectedRing.selected rho ∧
      RuntimeTransferCofactor.subgroupOrder • selectedRing = 0 ∧ selectedRing ≠ 0 := by
  have joinedSat : Satisfies rho RuntimeRnkJoined.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have ringSat : Satisfies rho RuntimeSelectedRingSubgroup.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  obtain ⟨q,r,senderBase,qBound,positive,rBound,noWrap,ivkHash,baseRole,subgroup,nonidentity,
    dhRole,hash,commitment,branches⟩ :=
      RuntimeRnkJoined.actual_ivk_dh_hash rho one four codec model standardOrder joinedSat
  obtain ⟨selectedRing,ringRole,ringSubgroup,ringNonidentity⟩ :=
    RuntimeSelectedRingSubgroup.actual_selected_subgroup rho one four model standardOrder ringSat
  rw [selected_input_values rho,← ringRole] at hash
  exact ⟨q,r,senderBase,selectedRing,qBound,positive,rBound,noWrap,ivkHash,baseRole,subgroup,
    nonidentity,dhRole,hash,commitment,branches,ringRole,ringSubgroup,ringNonidentity⟩
#print axioms selected_input_values
#print axioms actual_rnk_points
end ShielddSecurity.RuntimeRnkPoints
'''
    return _signature_audits(source)


def generate_selection(data, extracted, expected_relation, ivk_handles, expected_rnk_bindings):
    """Kernel-check the two branches against seven exact extracted rows."""
    from .generate_hash_round import linear, _signature_audits
    state = inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    if extracted.get('metadata_sha256') != hashlib.sha256(data).hexdigest():
        raise relation.RelationError('RNK selection metadata identity mismatch')
    identity = extracted.get('identity',{})
    if (identity.get('relation_digest') != expected_relation or identity.get('domain_size') != state['metadata']['domain_size']
            or identity.get('stored_rows') != state['metadata']['full_rows']):
        raise relation.RelationError('RNK selection relation identity mismatch')
    rows = {}
    for row in extracted['selected_rows']:
        if not isinstance(row,dict) or set(row) != {'row','a','b'}:
            raise relation.RelationError('malformed RNK selection row')
        i = relation.natural(row['row'],identity['stored_rows'])
        if i in rows: raise relation.RelationError('duplicate RNK selection row')
        for k in ('a','b'): relation.terms(row[k],identity['domain_size'])
        rows[i] = row
    roles = extracted['roles']
    if len(rows) != 7 or set(roles) != {'boolean','copy','selector','gate'} or len(roles['selector']) != 2 or len(roles['gate']) != 3:
        raise relation.RelationError('wrong RNK selection row/role shape')
    if set(rows) != {roles['boolean'],roles['copy'],*roles['selector'],*roles['gate']}:
        raise relation.RelationError('RNK selection row/role inventory mismatch')
    def parse(ts):return tuple((c,int(v,16)) for c,v in ts)
    def lc(ref):
        if not isinstance(ref,dict) or set(ref) != {'source'}:
            raise relation.RelationError('RNK selection requires captured Source roles')
        return state['observed'][source_index(ref['source'])]
    b = state['metadata']['rnk_bindings']
    values = dict(regulated=lc(b['regulated']),nk=state['observed'][tuple(ivk_handles[0])],
                  rnk=lc(b['hash']),commitment=lc(b['commitment']),registered=lc(b['registered']),effective=lc(b['effective_nk']),
                  gateOutput=parse(extracted['gate_output']),gateAux=parse(rows[roles['gate'][0]]['b']),
                  selectorOutput=canonical(lc(b['effective_nk'])+tuple((c,-v) for c,v in state['observed'][tuple(ivk_handles[0])])),
                  selectorAux=parse(rows[roles['selector'][0]]['b']))
    source=f'''import ShielddSecurity.ScalarComparisonBounds
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeRnkSelection
-- Actual ordinary relation: {expected_relation}
-- Extraction input SHA256: {hashlib.sha256(data).hexdigest()}
def modulus : Nat := {P}
def originalRows : List Nat := {sorted(rows)}
def rawRows : List Row := [
'''+',\n'.join('  ⟨'+linear(parse(rows[i]['a']))+', '+linear(parse(rows[i]['b']))+'⟩' for i in sorted(rows))+']\n'
    source+=''.join(f'def {name} : Linear := {linear(value)}\n' for name,value in values.items())
    source+='''
theorem regulated_boolean {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho regulated = 0 ∨ eval rho regulated = 1 := by
  apply boolean_sound
  exact Compiler.checked_row_sound rho rawRows ⟨regulated,regulated⟩ satisfied (by decide)

theorem actual_equations {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho regulated * (eval rho commitment - eval rho registered) = 0 ∧
    eval rho effective = eval rho nk + eval rho regulated * (eval rho rnk - eval rho nk) := by
  have gate := Compiler.checked_product_sound rho rawRows regulated
    (Compiler.subtract commitment registered) gateOutput gateAux four satisfied (by decide) (by decide)
  have zero := ScalarComparisonBounds.checked_equality rho rawRows satisfied gateOutput [] (by decide)
  have select := Compiler.checked_product_sound rho rawRows regulated
    (Compiler.subtract rnk nk) selectorOutput selectorAux four satisfied (by decide) (by decide)
  have difference := Compiler.canonical_equal rho selectorOutput (Compiler.subtract effective nk) (by decide)
  rw [Compiler.eval_subtract] at gate select difference
  constructor
  · exact gate.symm.trans (zero.trans (by simp [eval]))
  · rw [difference] at select
    exact (sub_eq_iff_eq_add.mp select).trans (by ring)

theorem actual_branches {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    (eval rho regulated = 0 ∧ eval rho effective = eval rho nk) ∨
    (eval rho regulated = 1 ∧ eval rho commitment = eval rho registered ∧
      eval rho effective = eval rho rnk) := by
  obtain ⟨gate,select⟩ := actual_equations rho four satisfied
  rcases regulated_boolean rho satisfied with unregulated | regulated
  · left
    exact ⟨unregulated,by simpa only [unregulated,zero_mul,add_zero] using select⟩
  · right
    rw [regulated,one_mul] at gate select
    exact ⟨regulated,sub_eq_zero.mp gate,by linear_combination select⟩
#print axioms regulated_boolean
#print axioms actual_equations
#print axioms actual_branches
end ShielddSecurity.RuntimeRnkSelection
'''
    # A polynomial rearrangement needs only the already-imported ring tactic.
    source=source.replace('by linear_combination select','by calc\n      _ = eval rho nk + (eval rho rnk - eval rho nk) := select\n      _ = _ := by ring')
    return _signature_audits(source)


def generate_dh_sponge_join():
    """Common-assignment DH/IVK/hash join; selected-ring interpretation stays open."""
    from .transfer_ownership import generate_rnk_ivk_join
    from .generate_hash_round import _signature_audits
    previous = generate_rnk_ivk_join()
    signature = previous.split('theorem actual_ivk_rnk', 1)[1].split(' := by', 1)[0]
    signature = signature.replace('RuntimeTransferRnkLoop.modulus', 'modulus')
    source = '''import ShielddSecurity.RuntimeTransferRnkIvk
import ShielddSecurity.RuntimeRnkInverse
import ShielddSecurity.RuntimeRnkSponge
set_option maxHeartbeats 800000
namespace ShielddSecurity.RuntimeRnkJoined
def modulus : Nat := RuntimeTransferRnkLoop.modulus
def rawRows : List Row := RuntimeTransferRnkIvk.rawRows ++
  (RuntimeRnkInverse.rawRows ++ RuntimeRnkSponge.rawRows)

theorem dh_input_columns :
    RuntimeRnkSponge.inputs.take 2 = [[(3763, (1 : Int))], [(3764, (1 : Int))]] := rfl

theorem actual_dh_nonidentity {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    RuntimeRnkInverse.point rho ≠ Group.identityPoint := by
  apply RuntimeRnkInverse.output_nonidentity rho one four
  intro row member
  exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))

theorem actual_ivk_dh''' + signature + ''' := by
  apply RuntimeTransferRnkIvk.actual_ivk_rnk rho one four codec model standardOrder
  intro row member
  exact satisfied row (List.mem_append.mpr (Or.inl member))

theorem actual_hash_and_commitment {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho RuntimeRnkSponge.output =
      Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters)
        17 (RuntimeRnkSponge.inputs.map (eval rho)) ∧
    eval rho RuntimeRnkSponge.commitment =
      Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters)
        18 [eval rho RuntimeRnkSponge.output] := by
  have hashSat : Satisfies rho RuntimeRnkSponge.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
  exact ⟨RuntimeRnkSponge.actual_rnk_hash rho one hashSat,
    RuntimeRnkSponge.actual_rnk_commitment rho one hashSat⟩

theorem actual_regulated_branches {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    (eval rho RuntimeRnkSelection.regulated = 0 ∧
      eval rho RuntimeRnkSelection.effective = eval rho RuntimeRnkSelection.nk) ∨
    (eval rho RuntimeRnkSelection.regulated = 1 ∧
      eval rho RuntimeRnkSponge.commitment = eval rho RuntimeRnkSelection.registered ∧
      eval rho RuntimeRnkSelection.effective = eval rho RuntimeRnkSponge.output) := by
  apply RuntimeRnkSponge.actual_regulated_branches rho four
  intro row member
  exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
#print axioms dh_input_columns
#print axioms actual_dh_nonidentity
#print axioms actual_ivk_dh
#print axioms actual_hash_and_commitment
#print axioms actual_regulated_branches
end ShielddSecurity.RuntimeRnkJoined
'''
    joined = '''
theorem dh_input_values {F : Type} [Field F] (rho : Nat → F) :
    RuntimeRnkSponge.inputs.map (eval rho) =
      [(RuntimeRnkTrace112.window13_output rho).x,
       (RuntimeRnkTrace112.window13_output rho).y] ++
      ((RuntimeRnkSponge.inputs.drop 2).map (eval rho)) := rfl

theorem actual_ivk_dh_hash''' + signature + ''' ∧
      eval rho RuntimeRnkSponge.output =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation0_0.parameters)
          17 ([(model.coordinates (r • senderBase)).x,
               (model.coordinates (r • senderBase)).y] ++
              ((RuntimeRnkSponge.inputs.drop 2).map (eval rho))) ∧
      eval rho RuntimeRnkSponge.commitment =
        Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_authorization_rnk_permutation2_0.parameters)
          18 [eval rho RuntimeRnkSponge.output] ∧
      ((eval rho RuntimeRnkSelection.regulated = 0 ∧
        eval rho RuntimeRnkSelection.effective = eval rho RuntimeRnkSelection.nk) ∨
       (eval rho RuntimeRnkSelection.regulated = 1 ∧
        eval rho RuntimeRnkSponge.commitment = eval rho RuntimeRnkSelection.registered ∧
        eval rho RuntimeRnkSelection.effective = eval rho RuntimeRnkSponge.output)) := by
  obtain ⟨q,r,senderBase,qBound,positive,rBound,noWrap,ivkHash,baseRole,subgroup,nonidentity,dhRole⟩ :=
    actual_ivk_dh rho one four codec model standardOrder satisfied
  obtain ⟨hash,commitment⟩ := actual_hash_and_commitment rho one satisfied
  rw [dh_input_values rho,dhRole] at hash
  exact ⟨q,r,senderBase,qBound,positive,rBound,noWrap,ivkHash,baseRole,subgroup,nonidentity,
    dhRole,hash,commitment,actual_regulated_branches rho four satisfied⟩
#print axioms dh_input_values
#print axioms actual_ivk_dh_hash
'''
    source = source.replace('end ShielddSecurity.RuntimeRnkJoined', joined + 'end ShielddSecurity.RuntimeRnkJoined')
    return _signature_audits(source)


def selection_controls(data, extracted, expected_relation, ivk_handles, expected_rnk_bindings):
    """Seven-row gate omission; the chosen hash values are not hash witnesses."""
    generate_selection(data,extracted,expected_relation,ivk_handles,expected_rnk_bindings)
    state = inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    rows = {r['row']:r for r in extracted['selected_rows']}
    bindings,observed = state['metadata']['rnk_bindings'],state['observed']
    def lc(ref):return observed[source_index(ref['source'])]
    def unit(terms):
        if len(terms) != 1 or terms[0][1] != 1:
            raise relation.RelationError('RNK control requires unit source/product columns')
        return terms[0][0]
    reg,registered,nk = unit(lc(bindings['regulated'])),unit(lc(bindings['registered'])),unit(observed[tuple(ivk_handles[0])])
    gate_output = unit(tuple((c,int(v,16)) for c,v in extracted['gate_output']))
    selector_output = unit(canonical(lc(bindings['effective_nk'])+tuple((c,-v) for c,v in observed[tuple(ivk_handles[0])])) )
    gate_aux = unit(tuple((c,int(v,16)) for c,v in rows[extracted['roles']['gate'][0]]['b']))
    select_aux = unit(tuple((c,int(v,16)) for c,v in rows[extracted['roles']['selector'][0]]['b']))
    columns = {c for row in rows.values() for k in ('a','b') for c,_ in row[k]}
    def evaluate(terms,rho):return sum(rho[c]*v for c,v in terms)%P
    def assignment(registered_value):
        rho = dict.fromkeys(columns,0);rho.update({0:1,state['metadata']['constant_copy']:1,reg:1,nk:3,registered:registered_value})
        def set_lc(terms,target):
            pivots = [c for c,v in terms if c not in (0,reg,nk,registered,gate_output,selector_output,gate_aux,select_aux)]
            if not pivots: raise relation.RelationError('RNK control lacks independent hash LC pivot')
            c = pivots[0]; coefficient = dict(terms)[c]
            rho[c] = ((target-evaluate(terms,rho))*pow(coefficient,-1,P)+rho[c])%P
        set_lc(lc(bindings['hash']),5);set_lc(lc(bindings['commitment']),1)
        rho[gate_output]=(1-registered_value)%P;rho[selector_output]=2
        for role,column in (('gate',gate_aux),('selector',select_aux)):
            row=rows[extracted['roles'][role][0]]
            rho[column]=evaluate(tuple((c,int(v,16)) for c,v in row['a']),rho)**2%P
        return rho
    def rejected(rho):return [i for i,row in sorted(rows.items())
        if evaluate(tuple((c,int(v,16)) for c,v in row['a']),rho)**2%P != evaluate(tuple((c,int(v,16)) for c,v in row['b']),rho)]
    positive,mutant = assignment(1),assignment(0)
    omitted = extracted['roles']['gate'][2]
    if rejected(positive) or rejected(mutant) != [omitted] or evaluate(lc(bindings['commitment']),mutant)==mutant[registered]:
        raise relation.RelationError('RNK intended gate omission not observed')
    return {'metadata_sha256':hashlib.sha256(data).hexdigest(),
            'scope':'seven actual selection/gate rows only; hash/loop/IVK/full Transfer excluded',
            'selected_rows':sorted(rows),'positive':{'assignment':sorted(positive.items()),'rejected_rows':[]},
            'gate_omission':{'assignment':sorted(mutant.items()),'omitted_row':omitted,
                             'original_rejected_rows':[omitted],'remaining_rows_satisfied':True,
                             'regulated_commitment_mismatch':True}}


def extract_all_permutations(data, stream, parameter_root, expected_relation, ivk_handles,
                             expected_rnk_bindings, anchor_extracted):
    """Row-only recurrence for all three captured permutation boundaries.

    The candidate contiguous range is anchored by the observed first cone.
    Every accepted row is from the full digest-checked ordinary stream, and every
    captured output coordinate is checked. No source DAG is invented for blocks
    whose internals were not observed.
    """
    state = inspect_metadata(data,parameter_root,expected_relation,ivk_handles,expected_rnk_bindings)
    if state['block'] != 0 or anchor_extracted.get('metadata_sha256') != state['metadata_sha256']:
        raise relation.RelationError('all-permutation route requires the accepted block0 anchor')
    copies = [t['row'] for t in anchor_extracted['templates'] if t['roles'] == ['constant-copy']]
    if len(copies) != 1: raise relation.RelationError('ambiguous RNK permutation anchor copy')
    copy_rows = [row for row in anchor_extracted['selected_rows'] if row['row'] == copies[0]]
    if (len(copy_rows) != 1 or copy_rows[0]['a'] != [[0,f'{1:064x}'],[state['metadata']['constant_copy'],f'{P-1:064x}']]
            or copy_rows[0]['b'] != []):
        raise relation.RelationError('wrong RNK permutation anchor constant-copy row')
    anchor = sorted(r['row'] for r in anchor_extracted['selected_rows'] if r['row'] != copies[0])
    if not anchor or anchor != list(range(anchor[0],anchor[-1]+1)):
        raise relation.RelationError('RNK permutation anchor is not one contiguous physical block')
    descriptions = [(state['states'][0][2][0],6),(state['states'][0][2][1],6),(state['states'][1][2][0],3)]
    parameters = [poseidon_graph.parameters(parameter_root/('poseidon381-wide.json' if width == 6 else 'poseidon381.json'),width)
                  for _,width in descriptions]
    counts = []
    for (pair,width),params in zip(descriptions,parameters):
        graph = poseidon_graph.permutation(params,
                [(lc[0][1] if lc else 0) if all(c == 0 for c,_ in lc) else None for lc in pair[0]])
        counts.append(4*sum(graph['nodes'][power['fifth']]['kind'] != 'constant'
                            for segment in graph['segments'] for power in segment['powers'].values()))
    if len(anchor) != counts[0] or sum(counts) > 2048:
        raise relation.RelationError('RNK permutation candidate range bound mismatch')
    start,stop = anchor[0],anchor[0]+sum(counts)
    selected = []
    def observe(row):
        if start <= row['row'] < stop or row['row'] == copies[0]: selected.append(row)
    identity = relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size'] != state['metadata']['domain_size'] or identity['stored_rows'] != state['metadata']['full_rows']:
        raise relation.RelationError('RNK all-permutation ordinary shape mismatch')
    rows = {r['row']:r for r in selected}
    if len(rows) != sum(counts)+1:
        raise relation.RelationError('missing RNK permutation candidate physical rows')
    anchor_rows = {r['row']:r for r in anchor_extracted['selected_rows']}
    if any(rows.get(i) != r for i,r in anchor_rows.items()):
        raise relation.RelationError('RNK permutation anchor/full stream row mismatch')
    copy_column = state['metadata']['constant_copy']
    def unoutline(ts):return canonical((0 if c == copy_column else c,int(v,16)) for c,v in ts)
    blocks = []
    for block_index,((pair,width),params,count) in enumerate(zip(descriptions,parameters,counts)):
        block_rows = {i:rows[i] for i in range(start,start+count)}
        table = {}
        for i,row in block_rows.items(): table.setdefault(unoutline(row['a']),[]).append((unoutline(row['b']),i))
        used = set(); current = list(pair[0]); rounds = []
        def unique(a):
            candidates = table.get(a,[])
            if len(candidates) != 1: raise relation.RelationError('missing/ambiguous RNK recurrence row')
            b,i = candidates[0]
            if i in used: raise relation.RelationError('RNK recurrence reused nonlinear row')
            used.add(i);return b,i
        for index in range(65):
            before = list(current)
            shifted = [canonical(lc+((0,params['ark'][index][j]),)) for j,lc in enumerate(current)]
            transformed = list(shifted);fifths={};indices=[]
            for j,base in enumerate(shifted):
                if not (index < 4 or index >= 61 or j == 0): continue
                if all(c == 0 for c,_ in base):
                    n = base[0][1] if base else 0
                    transformed[j] = canonical([(0,pow(n,5,P))])
                    fifths[j] = dict(kind='constant',coefficient=n)
                else:
                    square,i = unique(base);fourth,k = unique(square)
                    aux,m = unique(canonical(fourth+tuple((c,-v) for c,v in base)))
                    plus,n = unique(canonical(fourth+base))
                    transformed[j] = canonical((c,v*pow(4,-1,P)) for c,v in canonical(plus+tuple((c,-v) for c,v in aux)))
                    ids=[i,k,m,n];indices.extend(ids)
                    fifths[j]=dict(kind='arithmetic',square=square,fourth=fourth,auxiliary=aux,rows=ids)
            current = [canonical((c,v*coefficient) for lc,coefficient in zip(transformed,row) for c,v in lc)
                       for row in params['mds']]
            rounds.append(dict(kind='round',chunk=0,index=index,before=before,shifted=shifted,
                               transformed=transformed,after=list(current),fifths=fifths,rows=sorted(indices)))
        if current != pair[1] or used != set(block_rows):
            raise relation.RelationError('RNK recurrence output lanes/row coverage mismatch')
        blocks.append(dict(block=block_index,width=width,parameters=params,segments=rounds,
                           selected_rows=[block_rows[i] for i in sorted(block_rows)]+[rows[copies[0]]],
                           scope='actual-row recurrence; unobserved source DAG not asserted'))
        start += count
    return {'identity':identity,'metadata_sha256':state['metadata_sha256'],'blocks':blocks,
            'scope':'three actual-row permutation recurrences; kernel/sponge/source interpretation joins open'}


def row_permutation_selection(data, extracted, block, parameter_root, expected_relation,
                              ivk_handles, expected_rnk_bindings):
    """Adapt row-only recurrences to the existing bounded round kernel emitter."""
    state = inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    block = relation.natural(block,3)
    if extracted.get('metadata_sha256') != hashlib.sha256(data).hexdigest():
        raise relation.RelationError('RNK row permutation metadata mismatch')
    identity = extracted.get('identity',{})
    if (identity.get('relation_digest') != expected_relation or identity.get('domain_size') != state['metadata']['domain_size']
            or identity.get('stored_rows') != state['metadata']['full_rows']):
        raise relation.RelationError('RNK row permutation relation mismatch')
    descriptions = extracted.get('blocks')
    if not isinstance(descriptions,list) or len(descriptions) != 3 or [x.get('block') for x in descriptions] != [0,1,2]:
        raise relation.RelationError('RNK row permutation block order mismatch')
    selected = descriptions[block]
    width = 6 if block < 2 else 3
    params = poseidon_graph.parameters(parameter_root/('poseidon381-wide.json' if width == 6 else 'poseidon381.json'),width)
    if selected.get('width') != width or selected.get('parameters') != params:
        raise relation.RelationError('RNK row permutation parameter mismatch')
    segments = copy.deepcopy(selected.get('segments'))
    if not isinstance(segments,list) or [x.get('index') for x in segments] != list(range(65)):
        raise relation.RelationError('RNK row permutation round order mismatch')
    for segment in segments:
        segment['fifths'] = normalize_fifths(segment.get('fifths'),width,segment['index'])
    boundary = state['states'][0][2][block] if block < 2 else state['states'][1][2][0]
    def vector(xs):return [tuple(tuple(term) for term in lc) for lc in xs]
    if vector(segments[0]['before']) != boundary[0] or vector(segments[-1]['after']) != boundary[1]:
        raise relation.RelationError('RNK row permutation captured endpoint mismatch')
    if any(vector(a['after']) != vector(b['before']) for a,b in zip(segments,segments[1:])):
        raise relation.RelationError('RNK row permutation adjacency mismatch')
    raw = {}
    for row in selected['selected_rows']:
        if not isinstance(row,dict) or set(row) != {'row','a','b'}:
            raise relation.RelationError('malformed RNK row permutation physical row')
        index = relation.natural(row['row'],identity['stored_rows'])
        if index in raw: raise relation.RelationError('duplicate RNK row permutation physical index')
        for k in ('a','b'): relation.terms(row[k],identity['domain_size'])
        raw[index] = tuple(tuple((c,int(v,16)) for c,v in row[k]) for k in ('a','b'))
    copy_column = state['metadata']['constant_copy']
    links = [i for i,pair in raw.items() if pair == (canonical([(0,1),(copy_column,-1)]),())]
    if len(links) != 1: raise relation.RelationError('missing RNK row permutation constant copy')
    if set(raw) != {links[0],*(i for segment in segments for i in segment['rows'])}:
        raise relation.RelationError('RNK row permutation row inventory mismatch')
    role = 'authorization.rnk_permutation'+str(block)
    return {'outline':copy_column,'constant_link':links[0],'rows':raw,'observations':{},
            'calls':[dict(role=role,parameters=params,segments=segments,
                          call=dict(graph=dict(width=width,arity=0,domain=17 if block < 2 else 18,inputs=[]),inputs=[]))],
            'scope':'actual-row permutation candidate; mandatory full-stream replay precedes qualification'}


def normalize_fifths(fifths, width, index):
    """Recover typed lane keys after JSON replay, rejecting omissions/collisions."""
    if not isinstance(fifths,dict):
        raise relation.RelationError('malformed RNK fifth certificate map')
    result = {}
    for key,value in fifths.items():
        if type(key) is int: lane = key
        elif isinstance(key,str) and key.isascii() and key.isdigit() and str(int(key)) == key:
            lane = int(key)
        else: raise relation.RelationError('noncanonical RNK fifth lane key')
        relation.natural(lane,width)
        if lane in result: raise relation.RelationError('duplicate RNK fifth lane')
        if not isinstance(value,dict) or value.get('kind') not in ('constant','arithmetic'):
            raise relation.RelationError('malformed RNK fifth certificate')
        result[lane] = value
    active = set(range(width)) if index < 4 or index >= 61 else {0}
    if set(result) != active:
        raise relation.RelationError('missing/extra active RNK fifth lane')
    return result


def generate_sponge_join(data, extracted, parameter_root, expected_relation, ivk_handles, expected_rnk_bindings,
                         *, include_selection=True):
    """Compose checked endpoints at one rho, optionally before selector construction.

    The default retains its original generated bytes. Hash-only rendering still
    requires the same typed boundary and all three actual permutation row
    selections; it does not infer the registered commitment assertion.
    """
    if type(include_selection) is not bool:
        raise relation.RelationError('RNK sponge selection rendering must be Boolean')
    from .generate_hash_round import linear, _signature_audits
    state = inspect_boundaries(data,expected_relation,ivk_handles,expected_rnk_bindings)
    for block in range(3):
        row_permutation_selection(data,extracted,block,parameter_root,expected_relation,ivk_handles,expected_rnk_bindings)
    inputs,output,_ = state['states'][0]
    _,commitment,_ = state['states'][1]
    source=f'''import ShielddSecurity.RuntimeRnkHash0_Composition
import ShielddSecurity.RuntimeRnkHash1_Composition
import ShielddSecurity.RuntimeRnkHash2_Composition
import ShielddSecurity.RuntimeRnkSelection
set_option maxHeartbeats 800000
namespace ShielddSecurity.RuntimeRnkSponge
-- Extraction input SHA256: {hashlib.sha256(data).hexdigest()}
-- Actual relation: {expected_relation}
def modulus : Nat := {P}
def rawRows : List Row := (First.rawRows ++ Second.rawRows) ++ (Third.rawRows ++ RuntimeRnkSelection.rawRows)
def inputs : List Linear := [{', '.join(linear(x) for x in inputs)}]
def firstInputs : List Linear := [{', '.join(linear(x) for x in inputs[:5])}]
def secondInputs : List Linear := [{', '.join(linear(x) for x in inputs[5:])}]
def output : Linear := {linear(output)}
def commitment : Linear := {linear(commitment)}

private theorem first_absorption {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    (fun column => eval rho (First.states 0 column)) =
      Poseidon.absorb (Poseidon.initial 17 9) (firstInputs.map (eval rho)) := by
  have checked : ∀ column : Fin 6, Compiler.canonical modulus (First.states 0 column) =
      Compiler.canonical modulus (Poseidon.absorbLinear (Poseidon.initialLinear 17 9) firstInputs column) := by decide
  calc
    _ = (fun column => eval rho (Poseidon.absorbLinear (Poseidon.initialLinear 17 9) firstInputs column)) := by
      funext column
      exact Compiler.canonical_equal rho _ _ (checked column)
    _ = _ := by rw [Poseidon.eval_absorbLinear,Poseidon.eval_initialLinear rho one]

private theorem second_absorption {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) :
    (fun column => eval rho (Second.states 0 column)) =
      Poseidon.absorb (fun column => eval rho (First.states 65 column)) (secondInputs.map (eval rho)) := by
  have checked : ∀ column : Fin 6, Compiler.canonical modulus (Second.states 0 column) =
      Compiler.canonical modulus (Poseidon.absorbLinear (First.states 65) secondInputs column) := by decide
  calc
    _ = (fun column => eval rho (Poseidon.absorbLinear (First.states 65) secondInputs column)) := by
      funext column
      exact Compiler.canonical_equal rho _ _ (checked column)
    _ = _ := Poseidon.eval_absorbLinear rho (First.states 65) secondInputs

private theorem commitment_absorption {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    (fun column => eval rho (Third.states 0 column)) =
      Poseidon.absorb (Poseidon.initial 18 1) [eval rho output] := by
  have checked : ∀ column : Fin 3, Compiler.canonical modulus (Third.states 0 column) =
      Compiler.canonical modulus (Poseidon.absorbLinear (Poseidon.initialLinear 18 1) [output] column) := by decide
  calc
    _ = (fun column => eval rho (Poseidon.absorbLinear (Poseidon.initialLinear 18 1) [output] column)) := by
      funext column
      exact Compiler.canonical_equal rho _ _ (checked column)
    _ = _ := by rw [Poseidon.eval_absorbLinear,Poseidon.eval_initialLinear rho one]; rfl

theorem actual_rnk_hash {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho output = Poseidon.hash6 (Poseidon.castParameters First.parameters) 17 (inputs.map (eval rho)) := by
  have firstSat : Satisfies rho First.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))
  have secondSat : Satisfies rho Second.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
  have first := First.permutation_sound rho one firstSat
  have second := Second.permutation_sound rho one secondSat
  have parameters_equal : Second.parameters = First.parameters := rfl
  rw [first_absorption rho one] at first
  rw [parameters_equal,second_absorption rho,first] at second
  have coordinate := congrArg (fun s : Poseidon.State F 6 => s ⟨1,by decide⟩) second
  change eval rho output = _ at coordinate
  simpa only [Poseidon.hash6,inputs,firstInputs,secondInputs,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,Poseidon.chunks5,Poseidon.sponge,List.foldl_cons,List.foldl_nil] using coordinate

theorem actual_rnk_commitment {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho commitment = Poseidon.hash3 (Poseidon.castParameters Third.parameters) 18 [eval rho output] := by
  have thirdSat : Satisfies rho Third.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
  have third := Third.permutation_sound rho one thirdSat
  rw [commitment_absorption rho one] at third
  have coordinate := congrArg (fun s : Poseidon.State F 3 => s ⟨1,by decide⟩) third
  change eval rho commitment = _ at coordinate
  simpa only [Poseidon.hash3,List.length_cons,List.length_nil,Poseidon.chunks2,
    Poseidon.sponge,List.foldl_cons,List.foldl_nil] using coordinate

theorem actual_regulated_branches {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    (eval rho RuntimeRnkSelection.regulated = 0 ∧ eval rho RuntimeRnkSelection.effective = eval rho RuntimeRnkSelection.nk) ∨
    (eval rho RuntimeRnkSelection.regulated = 1 ∧ eval rho commitment = eval rho RuntimeRnkSelection.registered ∧
      eval rho RuntimeRnkSelection.effective = eval rho output) := by
  have selectionSat : Satisfies rho RuntimeRnkSelection.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
  exact RuntimeRnkSelection.actual_branches rho four selectionSat
#print axioms actual_rnk_hash
#print axioms actual_rnk_commitment
#print axioms actual_regulated_branches
end ShielddSecurity.RuntimeRnkSponge
'''
    if not include_selection:
        # Keep the existing absorption/permutation proofs and their row-member
        # paths; only the independently constructed selector slice is omitted.
        source = source.replace('import ShielddSecurity.RuntimeRnkSelection\n', '')
        source = source.replace('Third.rawRows ++ RuntimeRnkSelection.rawRows', 'Third.rawRows ++ []')
        start = source.index('theorem actual_regulated_branches ')
        end = source.index('#print axioms actual_rnk_hash', start)
        source = source[:start] + source[end:]
        source = source.replace('#print axioms actual_regulated_branches\n', '')
        source = source.replace('ShielddSecurity.RuntimeRnkSponge', 'ShielddSecurity.RuntimeRnkHashOnly')
    for alias,index in (('First',0),('Second',1),('Third',2)):
        source=source.replace(alias+'.',f'RuntimeHashBlock_authorization_rnk_permutation{index}_0.')
    return _signature_audits(source)
