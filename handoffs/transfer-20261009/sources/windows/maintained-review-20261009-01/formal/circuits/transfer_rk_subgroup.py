"""Fresh bounded RK subgroup ingress, sharing maintained arithmetic/formulas.

Four-spool qualification is owned by the existing Rust exporter. This parser
consumes its accepted metadata plus already accepted caller roles. Source and
row checks here do not promote native/source contracts or full Transfer gates.
"""
import hashlib
import re
from . import transfer_relation as relation, transfer_ak_subgroup as ak
from . import transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index

P = relation.MODULUS
D = -10240 * pow(10241, -1, P) % P
SCOPE = 'bounded RK cofactor/on-curve/nonidentity source observation; row and native joins open'


def inspect_metadata(data, accepted_roles):
    if not isinstance(data, bytes) or len(data) > 1024*1024:
        raise relation.RelationError('RK subgroup metadata size bound')
    if (not isinstance(accepted_roles, dict) or not isinstance(accepted_roles.get('metadata'), dict)
            or not isinstance(accepted_roles.get('observed'), dict)):
        raise relation.RelationError('accepted authorization roles required')
    try:
        obj = relation.record(data)
    except RecursionError as error:
        raise relation.RelationError('RK subgroup JSON nesting bound') from error
    keys = {'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
            'ordinary_full_ordered_rows_equal','repeated_observations_equal','inputs','curve','doubles',
            'spans','nonidentity','nonidentity_product','expressions','nodes'}
    if (set(obj) != keys or obj['schema'] != 'shieldd-transfer-rk-subgroup-v1'
            or obj['family'] != 'transfer' or obj['scope'] != SCOPE):
        raise relation.RelationError('RK subgroup closed schema/scope mismatch')
    accepted = accepted_roles['metadata']
    if not isinstance(obj['relation_digest'],str) or not re.fullmatch('[0-9a-f]{64}',obj['relation_digest']):
        raise relation.RelationError('RK subgroup relation digest framing')
    domain, count = relation.natural(obj['domain_size']), relation.natural(obj['full_rows'])
    copy = relation.natural(obj['constant_copy'], domain)
    if (domain < 4 or domain & (domain-1) or not 0 < count <= domain or copy < 3
            or obj['ordinary_full_ordered_rows_equal'] is not True
            or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('RK subgroup relation shape/parity mismatch')
    if (obj['relation_digest'] != accepted.get('relation_digest') or
            any(relation.natural(accepted.get(k)) != obj[k]
                for k in ('domain_size','full_rows','constant_copy'))):
        raise relation.RelationError('RK subgroup/authorization identity mismatch')
    def handles(values, size):
        if not isinstance(values,list) or len(values) != size:
            raise relation.RelationError('RK subgroup handle shape')
        return tuple(source_index(v) for v in values)
    inputs, curve, nonidentity = handles(obj['inputs'],5), handles(obj['curve'],2), handles(obj['nonidentity'],2)
    product = source_index(obj['nonidentity_product'])
    spend = accepted.get('spend')
    if not isinstance(spend,dict) or not isinstance(spend.get('rk'),list) or len(spend['rk']) != 2:
        raise relation.RelationError('accepted RK roles absent')
    rk = tuple(source_index(v.get('source') if isinstance(v,dict) else None) for v in spend['rk'])
    if inputs[:2] != rk or any(tag != 1 for tag,_ in inputs[:4]) or len(set(inputs[:4])) != 4 or inputs[4][0] != 0:
        raise relation.RelationError('RK subgroup point/preimage/coefficient role mismatch')
    if nonidentity[0] != inputs[0] or nonidentity[1][0] != 1 or product[0] != 2:
        raise relation.RelationError('RK subgroup nonidentity roles mismatch')
    if not isinstance(obj['doubles'],list) or len(obj['doubles']) != 3 or not isinstance(obj['spans'],list) or len(obj['spans']) != 3:
        raise relation.RelationError('RK subgroup requires exactly three doubles')
    doubles = tuple(handles(v,4) for v in obj['doubles'])
    roots = set(inputs+curve+nonidentity+(product,)); previous = inputs[2:4]; end = None
    for double,span in zip(doubles,obj['spans']):
        if double[:2] != previous or any(tag != 2 for tag,_ in double[2:]):
            raise relation.RelationError('RK subgroup double chain mismatch')
        if not isinstance(span,list) or len(span) != 2:
            raise relation.RelationError('RK subgroup span shape')
        start,stop = (relation.natural(v,2**32) for v in span)
        if not start < stop or stop-start > 128 or end is not None and start != end or stop != max(i for _,i in double[2:])+1:
            raise relation.RelationError('RK subgroup bounded allocation span mismatch')
        roots.update(double); roots.update((2,i) for i in range(start,stop)); previous=double[2:]; end=stop
    if any(tag != 2 for tag,_ in curve) or obj['spans'][0][0] != max(i for _,i in curve)+1 or product != (2,end):
        raise relation.RelationError('RK subgroup curve/inverse allocation boundary mismatch')
    observed = _expressions(obj['expressions'],domain,copy,1024,'RK subgroup')
    if observed.get(inputs[4]) != ((0,D),):
        raise relation.RelationError('RK subgroup coefficient mismatch')
    records = obj['nodes']
    if not isinstance(records,list) or len(records) > 2048:
        raise relation.RelationError('RK subgroup source node bound')
    nodes={}; last=-1
    for node in records:
        if not isinstance(node,dict) or set(node) != {'index','multiply','left','right'}:
            raise relation.RelationError('RK subgroup source node shape')
        index=relation.natural(node['index'],2**32); left,right=source_index(node['left']),source_index(node['right'])
        if index <= last or type(node['multiply']) is not bool or any(t == 2 and i >= index for t,i in (left,right)):
            raise relation.RelationError('RK subgroup source topology/order mismatch')
        nodes[(2,index)]=(node['multiply'],left,right); last=index
    if nodes.get(product) != (True,nonidentity[1],nonidentity[0]):
        raise relation.RelationError('RK subgroup inverse product source mismatch')
    pending=list(roots); visited=set(); required=set(roots)
    while pending:
        source=pending.pop()
        if source in visited: continue
        visited.add(source)
        if len(visited) > 2048: raise relation.RelationError('RK subgroup source closure bound')
        if source[0] == 2:
            if source not in nodes: raise relation.RelationError('RK subgroup missing source node')
            multiply,left,right=nodes[source]
            if multiply and left[0] != 0 and right[0] != 0: required.update((source,left,right))
            pending.extend((left,right))
        else: required.add(source)
    if set(nodes) != {h for h in visited if h[0] == 2} or set(observed) != required:
        raise relation.RelationError('RK subgroup exact graph/LC coverage mismatch')
    derived={}
    for source in sorted(visited):
        if source[0] != 2: derived[source]=observed[source]; continue
        multiply,left,right=nodes[source]
        value=combine(derived[left],derived[right]) if not multiply else None
        if multiply:
            for const,other in ((derived[left],derived[right]),(derived[right],derived[left])):
                if all(c == 0 for c,_ in const):
                    factor=const[0][1] if const else 0
                    value=canonical((c,v*factor) for c,v in other); break
            if value is None: value=observed[source]
        if source in observed and observed[source] != value:
            raise relation.RelationError('RK subgroup affine/observed LC mismatch')
        derived[source]=value
    for handle in set(observed) & set(accepted_roles['observed']):
        if observed[handle] != accepted_roles['observed'][handle]:
            raise relation.RelationError('RK subgroup shared source LC mismatch')
    state=dict(metadata=obj,inputs=inputs,curve=curve,doubles=doubles,nonidentity=nonidentity,
               nonidentity_product=product,observed=observed,derived=derived,nodes=nodes)
    # Reuse the maintained independent curve/shared-inverse/x/y formula matcher;
    # no AK metadata, IVK role or fictitious caller observation is synthesized.
    state['formulas']=ak.match_formulas(state)
    state['formulas']['scope']='bounded RK source formulas only; actual rows/native/constructive joins separate'
    owned_witnesses=set(inputs[2:4]+nonidentity[1:]+tuple(state['formulas']['inverse_witnesses']))
    external_columns={c for terms in accepted_roles['observed'].values() for c,_ in terms}
    if any(3+i in external_columns for _,i in owned_witnesses):
        raise relation.RelationError('RK subgroup witness/caller allocation alias')
    return state


def extract(data, accepted_roles, stream):
    state=inspect_metadata(data,accepted_roles); obj=state['metadata']; derived=state['derived']; copy=obj['constant_copy']
    outline=lambda lc:canonical((copy if c == 0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}; products=[]
    def require(role,a,b=()):required.setdefault((outline(a),outline(b)),[]).append(role)
    require('curve',combine(derived[state['curve'][0]],derived[state['curve'][1]],-1))
    for axis in range(2):
        require('rk-link.'+str(axis),combine(derived[state['inputs'][axis]],derived[state['doubles'][-1][axis+2]],-1))
    for index,product in enumerate(state['formulas']['inverse_assert_products']+[state['nonidentity_product']]):
        require('inverse-assert.'+str(index),combine(derived[product],[(0,1)],-1))
    for source,(multiply,left,right) in state['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0:continue
        a,b,z=derived[left],derived[right],derived[source]; role='node.'+str(source[1])
        if left == right:require(role+'.square',a,z)
        else:products.append((role,outline(combine(a,b,-1)),outline(combine(a,b)),outline(z),None))
    # The shared extractor retains its chosen certificates. Also retain every
    # bounded candidate in this SAME validated stream, so a duplicate producer
    # cannot disappear from the subsequent allocation-uniqueness check.
    targets=set()
    for source,(multiply,left,right) in state['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0:continue
        a,b=derived[left],derived[right]
        targets.add(a if left == right else combine(a,b,-1));targets.add(combine(a,b))
        targets.add(canonical((c,-v) for c,v in combine(a,b,-1)))
    candidates={}; candidate_counts={}
    class CandidateStream:
        def readline(self):
            line=stream.readline()
            if line:
                record=relation.record(line)
                if 'row' in record:
                    # Canonical row framing/identity is validated by the shared
                    # relation reader before any extraction result is returned.
                    for axis in ('a','b'):relation.terms(record.get(axis),obj['domain_size'])
                    row=tuple(canonical((0 if c == copy else c,int(v,16)) for c,v in record[axis]) for axis in ('a','b'))
                    if row[0] in targets:
                        key=relation.natural(record['row'],obj['full_rows'])
                        candidate_counts[row[0]]=candidate_counts.get(row[0],0)+1
                        if candidate_counts[row[0]] > 256 or len(candidates) >= 4096:
                            raise relation.RelationError('RK subgroup exact candidate bound')
                        candidates[key]=row
            return line
        def read(self,*args):return stream.read(*args)
    selected=arithmetic.extract_templates(CandidateStream(),obj['relation_digest'],obj['domain_size'],obj['full_rows'],
                                         required,products,[],label='RK subgroup')
    selected.update(metadata_sha256=hashlib.sha256(data).hexdigest(),
                    scope='exact RK subgroup source/formula and original rows only; constructive/native/whole Transfer joins open')
    # Revalidate every nonlinear row shape and retain its genuine compiler pivot.
    _,normalized=arithmetic.normalize_selection(selected,obj,selected['metadata_sha256'])
    stages=[]; external={c for terms in accepted_roles['observed'].values() for c,_ in terms}; written=set()
    witness_columns={3+i for _,i in state['inputs'][2:4]+state['nonidentity'][1:]+tuple(state['formulas']['inverse_witnesses'])}
    for source,(multiply,left,right) in state['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0:continue
        a,b,z=derived[left],derived[right],derived[source]
        certificate=arithmetic.product_certificate(a,b,z,normalized)
        if left == right:
            matches=[i for i,row in candidates.items() if row == (a,z)]
            if len(matches) != 1:raise relation.RelationError('RK subgroup square must have one exact actual match')
            pivots=[c for c,v in z if v == 1 and c not in {c for c,_ in a}]
            if len(pivots) != 1:raise relation.RelationError('RK subgroup square pivot shape')
            writes=[pivots[0]]
        else:
            minus,plus=combine(a,b,-1),combine(a,b)
            matches=[(x,y) for x,(difference,aux) in candidates.items()
                     if difference in (minus,canonical((c,-v) for c,v in minus))
                     for y,row in candidates.items() if x != y and row == (plus,combine(aux,z,4))]
            if len(matches) != 1:raise relation.RelationError('RK subgroup product must have one exact actual match')
            completion=arithmetic.product_completion_certificate(a,b,z,certificate,normalized)
            if completion is None:raise relation.RelationError('RK subgroup product allocation shape')
            writes=[completion['output'],completion['auxiliary']]
        if set(writes) & (external|witness_columns|written) or any(c in writes for c,_ in a+b):
            raise relation.RelationError('RK subgroup owned/caller/input allocation alias')
        written.update(writes); stages.append(dict(source=list(source),rows=certificate['rows'],writes=writes,kind=certificate['kind']))
    selected['allocation']=dict(witnesses=sorted(witness_columns),stages=stages,nonlinear_writes=sorted(written))
    return selected
