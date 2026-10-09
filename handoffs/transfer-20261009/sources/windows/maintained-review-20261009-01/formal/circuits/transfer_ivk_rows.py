"""Current IVK source-cone and compiler-LC checks; not a hash security proof.

The retained input handles are explicit semantic boundaries. Their ownership
and scalar-reduction meanings, actual row certificates, and whole Transfer
composition are separate joins. No witness values are evaluated here.
"""
import re
from . import transfer_relation as relation
from . import poseidon_graph
from .transfer_balance_rows import canonical, source_index

P = relation.MODULUS
SCOPE = 'source handles and pre-outline linear combinations only; semantic row certificates remain open'


def inspect_metadata(data, parameter_root, expected_relation):
    if not isinstance(expected_relation, str) or not re.fullmatch('[0-9a-f]{64}', expected_relation):
        raise relation.RelationError('exact canonical IVK relation digest required')
    if not isinstance(data, bytes) or len(data) > 4 * 1024 * 1024:
        raise relation.RelationError('IVK metadata exceeds 4MiB')
    obj = relation.record(data)
    keys = {'schema','relation_digest','domain_size','stored_rows','ordinary_full_ordered_rows_equal',
            'scope','constant_copy','domain','arity','handles','expressions','nodes'}
    if set(obj) != keys or obj['schema'] != 'shieldd-transfer-ivk-inspection-v1' or obj['scope'] != SCOPE:
        raise relation.RelationError('unknown IVK metadata schema/scope')
    if obj['relation_digest'] != expected_relation or obj['ordinary_full_ordered_rows_equal'] is not True:
        raise relation.RelationError('IVK relation identity/noninterference mismatch')
    domain = relation.natural(obj['domain_size'])
    count = relation.natural(obj['stored_rows'])
    if domain < 4 or domain & (domain-1) or not 0 < count <= domain:
        raise relation.RelationError('invalid IVK relation bounds')
    copy = relation.natural(obj['constant_copy'],domain)
    if copy < 3 or relation.natural(obj['domain'],256) != 16 or relation.natural(obj['arity']) != 3:
        raise relation.RelationError('wrong IVK domain/arity/constant copy')
    if not isinstance(obj['handles'],list) or len(obj['handles']) != 4:
        raise relation.RelationError('wrong IVK source handles')
    handles = [source_index(value) for value in obj['handles']]
    if len(set(handles)) != 4 or any(tag == 0 for tag,_ in handles):
        raise relation.RelationError('aliased/native IVK handles')
    if not isinstance(obj['expressions'],list) or not 4 <= len(obj['expressions']) <= 4096:
        raise relation.RelationError('wrong IVK expression collection')
    observed, previous = {}, (-1,-1)
    for item in obj['expressions']:
        if not isinstance(item,dict) or set(item) != {'source','terms'}:
            raise relation.RelationError('malformed IVK expression')
        source = source_index(item['source'])
        if source <= previous:
            raise relation.RelationError('noncanonical IVK expression ordering')
        previous = source
        relation.terms(item['terms'],domain)
        terms = tuple((column,int(value,16)) for column,value in item['terms'])
        if any(column == copy for column,_ in terms):
            raise relation.RelationError('outlined column in pre-outline expression')
        if source[0] == 0 and any(column != 0 for column,_ in terms):
            raise relation.RelationError('nonconstant source Constant LC')
        if source[0] == 1 and terms != ((3+source[1],1),):
            raise relation.RelationError('wrong exact compiler witness projection')
        observed[source] = terms
    if any(handle not in observed for handle in handles):
        raise relation.RelationError('missing IVK handle LC')
    if not isinstance(obj['nodes'],list) or len(obj['nodes']) > 16384:
        raise relation.RelationError('wrong IVK node collection')
    nodes, previous = {}, -1
    for item in obj['nodes']:
        if not isinstance(item,dict) or set(item) != {'index','multiply','left','right'}:
            raise relation.RelationError('malformed IVK node')
        index = relation.natural(item['index'],2**32)
        if index <= previous or type(item['multiply']) is not bool:
            raise relation.RelationError('noncanonical IVK node ordering/type')
        previous = index
        left,right = source_index(item['left']),source_index(item['right'])
        if any(tag == 2 and child >= index for tag,child in (left,right)):
            raise relation.RelationError('forward IVK source edge')
        nodes[(2,index)] = (item['multiply'],left,right)
    boundaries = set(handles[:3])
    pending, visited = [handles[3]], set()
    while pending:
        source = pending.pop()
        if source in visited: continue
        visited.add(source)
        if len(visited) > 16384: raise relation.RelationError('IVK source cone exceeds finite bound')
        if source in boundaries: continue
        if source[0] == 2:
            if source not in nodes: raise relation.RelationError('missing IVK source node')
            multiply,left,right = nodes[source]
            if multiply and left[0] != 0 and right[0] != 0 and any(item not in observed for item in (source,left,right)):
                raise relation.RelationError('missing nonlinear source/operand LC')
            pending.extend([left,right])
        elif source[0] == 0:
            if source not in observed: raise relation.RelationError('missing IVK source constant')
        else: raise relation.RelationError('undeclared IVK witness')
    if set(nodes) != {source for source in visited if source[0] == 2 and source not in boundaries}:
        raise relation.RelationError('extra IVK source nodes')
    required = set(handles) | {source for source in visited if source[0] == 0}
    for source,(multiply,left,right) in nodes.items():
        if multiply and left[0] != 0 and right[0] != 0: required.update([source,left,right])
    if set(observed) != required:
        raise relation.RelationError('missing/extra IVK selected expression')
    # Rename the retained boundary handles to formal input variables. This
    # discards their outside-cone computations explicitly, rather than inventing
    # observed source operations for those named semantic boundaries.
    names = {source:f'w{i}' for i,source in enumerate(handles[:3])}
    def name(source):
        return names.get(source,'cwn'[source[0]]+str(source[1]))
    abstract = {f'w{i}':{'kind':'witness'} for i in range(3)}
    derived = {handle:observed[handle] for handle in handles[:3]}
    for source in sorted(visited):
        if source in boundaries: continue
        if source[0] == 0:
            terms = observed[source]
            value = terms[0][1] if terms else 0
            abstract[name(source)] = {'kind':'constant','value':value}
            derived[source] = terms
        else:
            multiply,left,right = nodes[source]
            abstract[name(source)] = {'kind':'mul' if multiply else 'add','left':name(left),'right':name(right)}
            if multiply:
                folded = None
                for constant, other in ((derived[left],derived[right]),(derived[right],derived[left])):
                    if all(column == 0 for column,_ in constant):
                        factor = constant[0][1] if constant else 0
                        folded = canonical((column,value*factor) for column,value in other)
                        break
                if folded is not None:
                    derived[source] = folded
                    if source in observed and observed[source] != folded:
                        raise relation.RelationError('folded multiplication/compiler LC mismatch')
                elif source in observed:
                    derived[source] = observed[source]
                else:
                    raise relation.RelationError('missing nonlinear IVK output LC')
            else:
                derived[source] = canonical(derived[left]+derived[right])
                if source in observed and derived[source] != observed[source]:
                    raise relation.RelationError('source addition/compiler LC mismatch')
    params = poseidon_graph.parameters(parameter_root/'poseidon381-wide.json',6)
    graph = poseidon_graph.expected(params,16,3)
    pairs = poseidon_graph.match_source(graph,abstract,[f'w{i}' for i in range(3)],name(handles[3]))
    if {actual for _,actual in pairs} != set(abstract):
        raise relation.RelationError('unmatched extra IVK source cone')
    return {'metadata':obj,'handles':handles,'nodes':nodes,'observed':observed,'derived':derived,
            'graph':graph,'pairs':pairs,'source':abstract,
            'source_names':{source:name(source) for source in visited | boundaries},
            'scope':'source DAG/LC consistency only; multiplication row certificates and semantic role joins open'}


def extract(data, stream, parameter_root, expected_relation):
    """Select exact ordinary rows for the independently matched current IVK cone.

    This yields input for existing round/block generators, not a kernel verdict.
    Every selected row retains its original full-relation index. Compiler source
    interpretation, full row membership and upstream security remain distinct.
    """
    checked = inspect_metadata(data,parameter_root,expected_relation)
    copy = checked['metadata']['constant_copy']
    wanted = {canonical([(0,1),(copy,P-1)])}
    for source,(multiply,left,right) in checked['nodes'].items():
        if not multiply: continue
        left,right = checked['derived'][left],checked['derived'][right]
        if any(all(column == 0 for column,_ in terms) for terms in (left,right)): continue
        if left == right: wanted.add(left)
        else:
            wanted.add(canonical(left+tuple((column,-value) for column,value in right)))
            wanted.add(canonical(left+right))
    rows = []
    def observe(row):
        a = canonical((0 if column == copy else column,int(value,16)) for column,value in row['a'])
        if a in wanted or row['a'] == [[0,f'{1:064x}'],[copy,f'{P-1:064x}']]:
            if len(rows) >= 8192: raise relation.RelationError('IVK row selection exceeds finite bound')
            rows.append(row)
    identity = relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if (identity['domain_size'] != checked['metadata']['domain_size']
            or identity['stored_rows'] != checked['metadata']['stored_rows']):
        raise relation.RelationError('IVK metadata/full relation shape mismatch')
    source = {name:dict(node) for name,node in checked['source'].items()}
    for node in source.values():
        if node['kind'] == 'constant': node['value'] = f"{node['value']:064x}"
    names = checked['source_names']
    expressions = [{'source':names[index],'kind':'linear',
        'terms':[[column,f'{value:064x}'] for column,value in checked['derived'][index]]}
        for index in sorted(names)]
    export = {'hash_scope':'transfer-ivk-only','subject':'actual Transfer IVK hash dependency cone',
        'scalar_encoding':'canonical-big-endian-32','modulus_minus_one':f'{P-1:064x}',
        'relation_digest':expected_relation,'domain_size':identity['domain_size'],
        'row_count':identity['stored_rows'],'public_inputs':1,'committed_blocks':[1],
        'input_source_handles':checked['metadata']['handles'][:3],
        'input_role_provenance':'formal input renaming; original captured handles retained',
        'rows':[{'index':row['row'],'a':row['a'],'b':row['b']} for row in rows],
        'expressions':expressions,'calls':[{'role':'authorization.ivk','domain':16,
          'inputs':[names[index] for index in checked['handles'][:3]],
          'output':names[checked['handles'][3]],'source':source}]}
    return export
