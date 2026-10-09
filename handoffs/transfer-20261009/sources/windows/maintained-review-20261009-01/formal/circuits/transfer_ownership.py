"""Strict bounded ownership-chunk ingress; quotient/curve row joins stay open."""
import re
import hashlib
from . import transfer_relation as relation
from .transfer_balance_rows import source_index, canonical, combine

SCOPE = 'bounded first ownership variable-loop observation; source/row/group joins open'
RNK_SCOPE = 'bounded RNK-DH variable-loop observation; hash references are boundary-only; source/row/group joins open'


def inspect_rnk_metadata(data, expected_relation, expected_ivk_handles, expected_bits, expected_remainder):
    return inspect_metadata(data, expected_relation, expected_ivk_handles, expected_bits,
                            expected_remainder, _rnk=True)


def inspect_metadata(data, expected_relation, expected_ivk_handles, expected_bits, expected_remainder, *, _rnk=False):
    if not isinstance(expected_relation, str) or not re.fullmatch('[0-9a-f]{64}', expected_relation):
        raise relation.RelationError('exact canonical ownership relation digest required')
    if not isinstance(data, bytes) or len(data) > 2 * 1024 * 1024:
        raise relation.RelationError('ownership metadata exceeds 2MiB')
    obj = relation.record(data)
    keys = {'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
            'ivk_handles','remainder','remainder_bits','window_start','window_count','total_windows',
            'base','twice','triple','bits','output','target','windows','window_bits','quotients',
            'expressions','nodes'}
    if _rnk:
        keys = (keys - {'target'}) | {'nonidentity_inverse','rnk_bindings'}
    schema = 'shieldd-transfer-rnk-dh-v1' if _rnk else 'shieldd-transfer-ownership-v1'
    scope = RNK_SCOPE if _rnk else SCOPE
    if set(obj) != keys or obj['schema'] != schema or obj['family'] != 'transfer' or obj['scope'] != scope:
        raise relation.RelationError('unknown ownership schema/scope')
    if obj['relation_digest'] != expected_relation:
        raise relation.RelationError('ownership relation identity mismatch')
    domain = relation.natural(obj['domain_size'])
    count = relation.natural(obj['full_rows'])
    copy = relation.natural(obj['constant_copy'], domain)
    if domain < 4 or domain & (domain-1) or not 0 < count <= domain or copy < 3:
        raise relation.RelationError('invalid ownership relation bounds')
    start, count = relation.natural(obj['window_start'],126), relation.natural(obj['window_count'],17)
    if not 1 <= count <= 16 or start + count > 126 or type(obj['total_windows']) is not int or obj['total_windows'] != 126:
        raise relation.RelationError('invalid ownership chunk bounds')
    def handles(values, length):
        if not isinstance(values,list) or len(values) != length:
            raise relation.RelationError('wrong ownership handle collection')
        return tuple(source_index(v) for v in values)
    bits = handles(obj['bits'],252)
    if bits != handles(obj['remainder_bits'],252) or bits != handles(expected_bits,252) or len(set(bits)) != 252 or any(tag != 1 for tag,_ in bits):
        raise relation.RelationError('ownership/reduction bit role mismatch')
    ivk = handles(obj['ivk_handles'],4)
    remainder = source_index(obj['remainder'])
    if ivk != handles(expected_ivk_handles,4) or remainder[0] != 1 or remainder != source_index(expected_remainder):
        raise relation.RelationError('ownership IVK/remainder role mismatch')
    roots = set(bits)
    def observed(value, collect=True):
        if not isinstance(value,dict) or len(value) != 1:
            raise relation.RelationError('malformed ownership observed value')
        if set(value) == {'source'}:
            result = source_index(value['source'])
            if result[0] == 1 and 3 + result[1] >= domain:
                raise relation.RelationError('ownership witness source outside domain')
            if collect: roots.add(result)
            return ('source',result)
        if set(value) == {'native'} and isinstance(value['native'],str) and re.fullmatch('[0-9a-f]{64}',value['native']):
            result = int(value['native'],16)
            if result < relation.MODULUS: return ('native',result)
        raise relation.RelationError('noncanonical ownership native value')
    def pair(values):
        if not isinstance(values,list) or len(values) != 2:
            raise relation.RelationError('wrong ownership point collection')
        return tuple(observed(v) for v in values)
    points = {role:pair(obj[role]) for role in (('base','twice','triple','output') if _rnk else ('base','twice','triple','output','target'))}
    boundary = None
    if _rnk:
        inverse = observed(obj['nonidentity_inverse'])
        if inverse[0] != 'source' or inverse[1][0] != 1:
            raise relation.RelationError('RNK nonidentity inverse must be witness')
        binding = obj['rnk_bindings']
        if not isinstance(binding,dict) or set(binding) != {'inputs','hash','commitment','regulated','registered','effective_nk'}:
            raise relation.RelationError('unknown RNK boundary schema')
        if not isinstance(binding['inputs'],list) or len(binding['inputs']) != 9:
            raise relation.RelationError('wrong RNK boundary input arity')
        boundary = {key:observed(binding[key],False) for key in binding if key != 'inputs'}
        boundary['inputs'] = tuple(observed(value,False) for value in binding['inputs'])
        if boundary['inputs'][:2] != points['output']:
            raise relation.RelationError('RNK DH hash input role mismatch')
    if any(kind != 'source' or value[0] != 1 for role in (('base',) if _rnk else ('base','target')) for kind,value in points[role]):
        raise relation.RelationError('ownership address must use witness coordinates')
    if not isinstance(obj['windows'],list) or len(obj['windows']) != count or not isinstance(obj['window_bits'],list) or len(obj['window_bits']) != count:
        raise relation.RelationError('ownership window count mismatch')
    windows = []
    for offset,(window,wb) in enumerate(zip(obj['windows'],obj['window_bits'])):
        if not isinstance(window,list) or len(window) != 5:
            raise relation.RelationError('wrong ownership window shape')
        low = 2 * (125-start-offset)
        if handles(wb,2) != bits[low:low+2]:
            raise relation.RelationError('ownership reversed window bit order mismatch')
        parsed = tuple(pair(p) for p in window)
        if windows and parsed[0] != windows[-1][4]:
            raise relation.RelationError('ownership window point chain mismatch')
        windows.append(parsed)
    if start == 0 and windows[0][0] != (('native',0),('native',1)):
        raise relation.RelationError('ownership initial accumulator is not identity')
    if start+count == 126 and windows[-1][4] != points['output']:
        raise relation.RelationError('ownership final output role mismatch')
    if not isinstance(obj['quotients'],list) or len(obj['quotients']) != 2+3*count:
        raise relation.RelationError('ownership quotient count mismatch')
    quotients = []
    for values in obj['quotients']:
        if not isinstance(values,list) or len(values) != 6:
            raise relation.RelationError('wrong ownership quotient tuple')
        quotients.append(tuple(observed(v) for v in values))
    if quotients[0][4:] != points['twice'] or quotients[1][4:] != points['triple']:
        raise relation.RelationError('ownership precomputation quotient role mismatch')
    for offset,window in enumerate(windows):
        if tuple(q[4:] for q in quotients[2+3*offset:5+3*offset]) != (window[1],window[2],window[4]):
            raise relation.RelationError('ownership window quotient output mismatch')
    if not isinstance(obj['expressions'],list) or not 1 <= len(obj['expressions']) <= 4096:
        raise relation.RelationError('wrong ownership expression collection')
    expressions, previous = {}, (-1,-1)
    for item in obj['expressions']:
        if not isinstance(item,dict) or set(item) != {'source','terms'}:
            raise relation.RelationError('malformed ownership expression')
        source = source_index(item['source'])
        if source <= previous: raise relation.RelationError('noncanonical ownership expression order')
        previous = source
        relation.terms(item['terms'],domain)
        terms = tuple((column,int(value,16)) for column,value in item['terms'])
        if any(column == copy for column,_ in terms) or (source[0] == 0 and any(column != 0 for column,_ in terms)):
            raise relation.RelationError('wrong ownership constant/outline LC')
        if source[0] == 1 and terms != ((3+source[1],1),):
            raise relation.RelationError('wrong ownership witness coordinate')
        expressions[source] = terms
    if not roots <= set(expressions): raise relation.RelationError('missing ownership role LC')
    if not isinstance(obj['nodes'],list) or len(obj['nodes']) > 8192:
        raise relation.RelationError('wrong ownership node collection')
    nodes, previous = {}, -1
    for item in obj['nodes']:
        if not isinstance(item,dict) or set(item) != {'index','multiply','left','right'}:
            raise relation.RelationError('malformed ownership source node')
        index = relation.natural(item['index'],2**32)
        left,right = source_index(item['left']),source_index(item['right'])
        if index <= previous or type(item['multiply']) is not bool or any(tag == 2 and child >= index for tag,child in (left,right)):
            raise relation.RelationError('noncanonical ownership source topology')
        previous = index; nodes[(2,index)] = (item['multiply'],left,right)
    pending,visited,required=list(roots),set(),set(roots)
    while pending:
        source=pending.pop()
        if source in visited:continue
        visited.add(source)
        if len(visited)>8192:raise relation.RelationError('ownership source cone exceeds bound')
        if source[0]==2:
            if source not in nodes:raise relation.RelationError('missing ownership source node')
            multiply,left,right=nodes[source]
            if multiply and left[0]!=0 and right[0]!=0:required.update((source,left,right))
            pending.extend((left,right))
        else:required.add(source)
    if set(nodes)!={source for source in visited if source[0]==2} or set(expressions)!=required:
        raise relation.RelationError('missing/extra ownership graph or expression')
    derived={}
    for source in sorted(visited):
        if source[0]!=2:derived[source]=expressions[source];continue
        multiply,left,right=nodes[source]
        if not multiply:value=combine(derived[left],derived[right])
        else:
            value=None
            for const,other in ((derived[left],derived[right]),(derived[right],derived[left])):
                if all(column==0 for column,_ in const):
                    factor=const[0][1] if const else 0
                    value=canonical((column,coefficient*factor) for column,coefficient in other)
                    break
            if value is None:value=expressions[source]
        if source in expressions and value!=expressions[source]:
            raise relation.RelationError('ownership affine arithmetic/observed LC mismatch')
        derived[source]=value
    return {'metadata':obj,'metadata_sha256':hashlib.sha256(data).hexdigest(),'points':points,'windows':windows,'quotients':quotients,
            'bits':bits,'expressions':expressions,'nodes':nodes,'derived':derived,
            'rnk_boundary':boundary, 'nonidentity_inverse':inverse if _rnk else None,
            'scope':'closed chunk source/affine ingress; hash boundary refs unexpanded; formula/nonlinear actual-row joins pending' if _rnk else 'closed chunk source/affine ingress; formula/nonlinear actual-row joins pending'}


def expected_formula(kind, axis, inputs):
    """Independent optimized affine numerator/denominator/selector source graph.

    Native operands are folded and reordered exactly as Var.merge. Source
    inputs retain their slots. This does not assume division is total.
    """
    if axis not in ('x','y') or kind not in ('double.numerator','double.denominator',
            'add.numerator','add.denominator','select'):
        raise ValueError('unknown ownership formula')
    wanted = 2 if kind.startswith('double.') else 4 if kind.startswith('add.') else 8
    if len(inputs) != wanted: raise ValueError('wrong ownership formula input count')
    nodes, native, source_inputs = [], [], []
    def put(value, is_native=False):
        nodes.append(value);native.append(is_native);return len(nodes)-1
    def constant(value, is_native=False):
        return put({'kind':'constant','value':value%relation.MODULUS},is_native)
    values=[]
    for value in inputs:
        if value[0] == 'native': values.append(constant(value[1],True))
        elif value[0] == 'source':
            values.append(put({'kind':'input','slot':len(source_inputs)}));source_inputs.append(value[1])
        else: raise ValueError('wrong ownership observed input')
    def op(kind,left,right):
        a,b=nodes[left],nodes[right]
        if a['kind']==b['kind']=='constant':
            return constant(a['value']+b['value'] if kind=='add' else a['value']*b['value'],
                            native[left] and native[right])
        if native[right] and not native[left]:left,right=right,left
        return put({'kind':kind,'left':left,'right':right})
    def add(a,b):return op('add',a,b)
    def mul(a,b):return op('mul',a,b)
    def neg(b):
        if nodes[b]['kind']=='constant':return constant(-nodes[b]['value'],native[b])
        return mul(constant(-1),b)
    def sub(a,b):return add(a,neg(b))
    if kind.startswith('double.'):
        x,y=values;xx,yy=mul(x,x),mul(y,y)
        if kind=='double.numerator':
            total=add(x,y)
            output=sub(sub(mul(total,total),xx),yy) if axis=='x' else add(yy,xx)
        else:
            dx=sub(yy,xx)
            output=dx if axis=='x' else sub(constant(2,True),dx)
    elif kind.startswith('add.'):
        x,y,u,v=values;xx,yy=mul(x,u),mul(y,v)
        if kind=='add.numerator':
            output=sub(sub(mul(add(x,y),add(u,v)),xx),yy) if axis=='x' else add(yy,xx)
        else:
            d=(-10240*pow(10241,-1,relation.MODULUS))%relation.MODULUS
            dt=mul(mul(xx,yy),constant(d,True));one=constant(1,True)
            output=add(one,dt) if axis=='x' else sub(one,dt)
    else:
        bx,by,tx,ty,ux,uy,low,high=values
        def choose(bit,yes,no):return add(no,mul(bit,sub(yes,no)))
        output=choose(high,choose(low,ux,tx),choose(low,bx,constant(0,True))) if axis=='x' else \
            choose(high,choose(low,uy,ty),choose(low,by,constant(1,True)))
    return {'arity':len(source_inputs),'nodes':nodes,'output':output},source_inputs


def match_formulas(checked):
    """Check bounded source cones against the independent optimized formulas.

    Quotient witnesses have no division semantics here: their materialized
    product/equality rows and nonzero denominators are subsequent obligations.
    """
    from . import poseidon_graph
    def name(handle):return 'cwn'[handle[0]]+str(handle[1])
    source={}
    for handle,terms in checked['expressions'].items():
        if handle[0]==0:source[name(handle)]={'kind':'constant','value':terms[0][1] if terms else 0}
        elif handle[0]==1:source[name(handle)]={'kind':'witness'}
    for handle,(multiply,left,right) in checked['nodes'].items():
        source[name(handle)]={'kind':'mul' if multiply else 'add','left':name(left),'right':name(right)}
    cones=[]
    def match(kind,axis,inputs,output):
        graph,roles=expected_formula(kind,axis,inputs)
        if output[0]=='native':
            # Fully folded native expressions must be closed constants.
            node=graph['nodes'][graph['output']]
            if graph['arity'] or node!={'kind':'constant','value':output[1]}:
                raise relation.RelationError('ownership native formula mismatch')
            pairs=[]
        else:
            try:pairs=poseidon_graph.match_source(graph,source,[name(r) for r in roles],name(output[1]))
            except ValueError as error:
                raise relation.RelationError('ownership '+kind+'.'+axis+' source formula mismatch: '+str(error)) from error
        cones.append({'kind':kind,'axis':axis,'inputs':inputs,'output':output,'graph':graph,'pairs':pairs})
    def quotient(kind,inputs,q):
        for offset,part in ((0,'numerator'),(2,'denominator')):
            for i,axis in enumerate(('x','y')):match(kind+'.'+part,axis,inputs,q[offset+i])
    p=checked['points'];q=checked['quotients']
    quotient('double',p['base'],q[0])
    quotient('add',p['twice']+p['base'],q[1])
    start=checked['metadata']['window_start']
    for offset,window in enumerate(checked['windows']):
        first,second,third=q[2+3*offset:5+3*offset]
        quotient('double',window[0],first)
        quotient('double',window[1],second)
        quotient('add',window[2]+window[3],third)
        low=2*(125-start-offset)
        selector=p['base']+p['twice']+p['triple']+tuple(('source',b) for b in checked['bits'][low:low+2])
        for axis,output in zip(('x','y'),window[3]):match('select',axis,selector,output)
    return {'cones':cones,'source':source,
            'scope':'source formula correspondence only; quotient/curve/Boolean actual-row proofs pending'}


def join_chunks(chunks):
    if not isinstance(chunks,list) or not 1<=len(chunks)<=126:
        raise relation.RelationError('wrong ownership chunk collection')
    expected=0;first=chunks[0];previous=None;common={};common_nodes={}
    header_keys=('relation_digest','domain_size','full_rows','constant_copy','ivk_handles',
                 'remainder','remainder_bits','total_windows','bits','base','twice','triple','output','target')
    if first['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1':
        header_keys = tuple(key for key in header_keys if key != 'target') + ('schema','scope','nonidentity_inverse','rnk_bindings')
    for chunk in chunks:
        metadata=chunk['metadata']
        if metadata['window_start']!=expected:
            raise relation.RelationError('ownership chunks omit/reorder/duplicate windows')
        if any(metadata[key]!=first['metadata'][key] for key in header_keys):
            raise relation.RelationError('ownership chunk header/role mismatch')
        if chunk['quotients'][:2]!=first['quotients'][:2]:
            raise relation.RelationError('ownership precomputation source mismatch')
        if previous is not None and chunk['windows'][0][0]!=previous:
            raise relation.RelationError('ownership cross-chunk point mismatch')
        for source,lc in chunk['expressions'].items():
            if source in common and common[source]!=lc:
                raise relation.RelationError('ownership shared source LC mismatch')
            common[source]=lc
        for source,node in chunk['nodes'].items():
            if source in common_nodes and common_nodes[source]!=node:
                raise relation.RelationError('ownership shared source node mismatch')
            common_nodes[source]=node
        expected+=metadata['window_count'];previous=chunk['windows'][-1][4]
    if expected!=126:raise relation.RelationError('ownership chunks do not cover all126 windows')
    return {'windows':126,'chunks':len(chunks),'shared_expressions':common,'shared_nodes':common_nodes,
            'scope':'exact source/LC chunk coverage only; common-assignment kernel composition pending'}


def extract_rows(checked, stream, expected_relation, include_bits=False):
    """Recover actual arithmetic and Div assertions, without assuming division.

    Div creates a materialized quotient-times-denominator product and a separate
    equality to the numerator. Neither the quotient witness nor source formula
    matching establishes those rows or denominator nonzeroness.
    """
    match_formulas(checked)
    metadata, derived = checked['metadata'], checked['derived']
    if metadata['relation_digest'] != expected_relation:
        raise relation.RelationError('ownership row identity mismatch')
    p, copy = relation.MODULUS, metadata['constant_copy']
    def outline(lc):return canonical((copy if c == 0 else c,v) for c,v in lc)
    def observed(value):return derived[value[1]] if value[0] == 'source' else canonical([(0,value[1])])
    required, products, squares = {}, [], []
    def require(role,a,b=()):required.setdefault((outline(a),outline(b)),[]).append(role)
    required[(canonical([(0,1),(copy,p-1)]),())]=['constant-copy']
    if type(include_bits) is not bool:
        raise relation.RelationError('ownership bit extraction flag')
    if include_bits:
        start,count=metadata['window_start'],metadata['window_count']
        for index in range(2*(126-start-count),2*(126-start)):
            bit=derived[checked['bits'][index]]
            require('bit.'+str(index),bit,bit)
    for source,(multiply,left,right) in checked['nodes'].items():
        if not multiply or left[0] == 0 or right[0] == 0:continue
        a,b,out = derived[left],derived[right],derived[source]
        role='node.'+str(source[1])
        folded=next(((lc,other) for lc,other in ((a,b),(b,a))
                     if not lc or len(lc)==1 and lc[0][0]==0),None)
        if folded is not None:
            constant,other=folded
            coefficient=constant[0][1] if constant else 0
            if out!=canonical((c,v*coefficient) for c,v in other):
                raise relation.RelationError('ownership folded product LC mismatch')
            continue
        if a == b:require(role+'.square',a,out)
        else:products.append((role,outline(combine(a,b,-1)),outline(combine(a,b)),outline(out),None))
    for index,quotient in enumerate(checked['quotients']):
        for axis in range(2):
            numerator,denominator,q = map(observed,(quotient[axis],quotient[axis+2],quotient[axis+4]))
            role='quotient.'+str(index)+'.'+str(axis)
            # Constant multiplication compiles as an LC, including native 0/0.
            constant=next(((lc,other) for lc,other in ((denominator,q),(q,denominator))
                           if not lc or len(lc)==1 and lc[0][0]==0),None)
            if constant is not None:
                scalar_lc,other=constant
                factor=scalar_lc[0][1] if scalar_lc else 0
                product=canonical((c,v*factor) for c,v in other)
                equation=combine(product,numerator,-1)
                if equation:require(role+'.assertion',equation)
            elif q==denominator:
                squares.append((role,outline(q),outline(numerator)))
            else:
                products.append((role,outline(combine(q,denominator,-1)),outline(combine(q,denominator)),None,outline(numerator)))
    if metadata.get('schema') == 'shieldd-transfer-rnk-dh-v1':
        inverse = observed(checked['nonidentity_inverse'])
        output_x = observed(checked['points']['output'][0])
        # Var.inv emits inverse * value, then materialized-product == one.
        # Keep that source operand orientation and the separate assertion.
        products.append(('nonidentity',outline(combine(inverse,output_x,-1)),
                         outline(combine(inverse,output_x)),None,outline(((0,1),))))
    if metadata['window_start']+metadata['window_count']==126 and metadata.get('schema') != 'shieldd-transfer-rnk-dh-v1':
        for axis in range(2):require('target.'+str(axis),combine(observed(checked['points']['output'][axis]),observed(checked['points']['target'][axis]),-1))
    from .transfer_arithmetic import extract_templates
    result=extract_templates(stream,expected_relation,metadata['domain_size'],metadata['full_rows'],
                             required,products,squares,label='ownership')
    result['scope']='actual chunk row extraction only; denominator/group/kernel/source completion pending'
    return result


def generate_parameter_contract():
    """Discharge optimized-window parameter facts from the checked codec/params.

    RuntimeJubjub must be generated from the exact runtime parameter source and
    checked in the same dependency universe. This is not a native codec join.
    """
    return '''import ShielddSecurity.RuntimeJubjub
import ShielddSecurity.TransferReduction

set_option maxHeartbeats 100000

namespace ShielddSecurity.RuntimeTransferCurveParameters

theorem actual_curve_parameters {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) :
    Group.NoUnitSquare (RuntimeJubjub.d : F) ∧
      (RuntimeJubjub.imaginary : F) * (RuntimeJubjub.imaginary : F) = -1 ∧
      (RuntimeJubjub.d : F) = -(10240 : F) / 10241 := by
  letI : Fintype F := Fintype.ofEquiv (Fin Scalar.modulus)
    (TransferReduction.codec_equiv codec).symm
  exact ⟨RuntimeJubjub.nonsquare (TransferReduction.codec_cardinality codec),
    RuntimeJubjub.imaginary_square, RuntimeJubjub.runtime_coefficient⟩

set_option pp.all true in
#check @actual_curve_parameters
#print axioms actual_curve_parameters

end ShielddSecurity.RuntimeTransferCurveParameters
'''


def cone_certificates(checked, extracted, window_offset=0, include_precompute=True):
    """Select one window's local-node certificates, independently of chunk size.

    Extracted original rows and their source/LC correspondence remain an explicit
    boundary. The emitted kernel checks do not trust product role labels.
    """
    metadata=checked['metadata']
    relation.natural(window_offset,metadata['window_count'])
    if type(include_precompute) is not bool:
        raise relation.RelationError('ownership precompute selection must be Boolean')
    identity=extracted.get('identity',{})
    if (identity.get('relation_digest')!=metadata['relation_digest'] or
            identity.get('stored_rows')!=metadata['full_rows'] or
            identity.get('domain_size')!=metadata['domain_size']):
        raise relation.RelationError('ownership cone extraction identity/shape mismatch')
    copy=metadata['constant_copy'];raw={}
    for row in extracted.get('selected_rows',[]):
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:
            raise relation.RelationError('ownership cone row schema')
        index=relation.natural(row['row'],metadata['full_rows'])
        if index in raw:raise relation.RelationError('duplicate ownership cone row')
        for terms in (row['a'],row['b']):relation.terms(terms,metadata['domain_size'])
        raw[index]=tuple(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
    if len(raw)>8192:raise relation.RelationError('ownership cone row bound')
    table={};squared={}
    for index,row in sorted(raw.items()):
        a,b=(canonical((0 if c==copy else c,v) for c,v in lc) for lc in row)
        table.setdefault((a,b),index);squared.setdefault(a,[]).append((b,index))
    copy_key=(canonical([(0,1),(copy,-1)]),())
    copy_index=next((index for index,row in raw.items() if row==copy_key),None)
    if copy_index is None:raise relation.RelationError('missing ownership cone constant link')
    used={copy_index};matched=match_formulas(checked)
    observations={}
    def name(handle):return 'cwn'[handle[0]]+str(handle[1])
    for handle,lc in checked['derived'].items():observations[name(handle)]=('linear',lc)
    selected=list(range(8)) if include_precompute else []
    selected+=list(range(8+14*window_offset,8+14*(window_offset+1)))
    cones=[]
    for index in selected:
        cone=matched['cones'][index];graph,roles=expected_formula(cone['kind'],cone['axis'],cone['inputs'])
        source=matched['source'];inputs=[name(handle) for handle in roles]
        if cone['output'][0]=='native':
            output='native_'+str(index);value=cone['output'][1]
            source={output:{'kind':'constant','value':value}}
            observations[output]=('linear',canonical([(0,value)]));identities={output}
        else:
            output=name(cone['output'][1]);identities={identity for _,identity in cone['pairs']}
        ordered=[];visited=set()
        def visit(identity):
            if identity in visited:return
            visited.add(identity)
            node=source[identity]
            if identity not in inputs and node['kind'] in ('add','mul'):
                visit(node['left']);visit(node['right'])
            ordered.append(identity)
        for identity in inputs:visit(identity)
        visit(output)
        if visited!=identities|set(inputs):raise relation.RelationError('ownership cone source closure mismatch')
        certificates={}
        for identity in ordered:
            node=source[identity];out=observations[identity][1]
            if identity in inputs:certificate={'kind':'input'}
            elif node['kind']=='constant':certificate={'kind':'constant','coefficient':node['value']}
            else:
                left,right=(observations[node[side]][1] for side in ('left','right'))
                if node['kind']=='add':certificate={'kind':'add'}
                else:
                    constants=[(side,lc[0][1] if lc else 0) for side,lc in (('left',left),('right',right))
                               if all(column==0 for column,_ in lc)]
                    if constants:
                        side,value=constants[0];certificate={'kind':'folded_'+side,'coefficient':value}
                    elif left==right:
                        if (left,out) not in table:raise relation.RelationError('missing oriented ownership cone square')
                        certificate={'kind':'square','rows':[table[(left,out)]]}
                    else:
                        minus,plus=combine(left,right,-1),combine(left,right)
                        pairs=[(first,table[(plus,combine(aux,out,4))],aux)
                               for aux,first in squared.get(minus,[]) if (plus,combine(aux,out,4)) in table]
                        if not pairs:raise relation.RelationError('missing oriented ownership cone product')
                        first,second,aux=min(pairs)
                        certificate={'kind':'product','rows':[first,second],'auxiliary':aux}
                    used.update(certificate.get('rows',[]))
            certificates[identity]=certificate
        cones.append({'role':'formula'+str(index),'source':source,'inputs':inputs,'output':output,
                      'ordered':ordered,'certificates':certificates,'expected_graph':graph})
    return {'outline':copy,'rows':{index:raw[index] for index in sorted(used)},
            'cones':cones,'observations':observations}


def quotient_certificates(checked, extracted, window_offset=0, include_precompute=True):
    """Select bounded Div certificates, retaining the materialized equality.

    These are proof-generator inputs, not facts about an honest quotient. In
    particular a zero denominator is never ruled out by this selection.
    """
    metadata=checked['metadata'];p=relation.MODULUS;copy=metadata['constant_copy']
    if type(window_offset) is not int or not 0<=window_offset<metadata['window_count']:
        raise relation.RelationError('ownership quotient window offset')
    if type(include_precompute) is not bool:
        raise relation.RelationError('ownership quotient precompute flag')
    if (extracted['identity']['relation_digest']!=metadata['relation_digest'] or
        extracted['identity'].get('domain_size')!=metadata['domain_size'] or
        extracted['identity'].get('stored_rows')!=metadata['full_rows']):
        raise relation.RelationError('ownership quotient relation identity')
    if not isinstance(extracted['selected_rows'],list) or not 1<=len(extracted['selected_rows'])<=8192:
        raise relation.RelationError('ownership quotient selected row bound')
    raw={};normalized={}
    for row in extracted['selected_rows']:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:
            raise relation.RelationError('ownership quotient row schema')
        index=row['row']
        if type(index) is not int or not 0<=index<metadata['full_rows'] or index in raw:
            raise relation.RelationError('ownership quotient row identity')
        relation.terms(row['a'],metadata['domain_size'])
        relation.terms(row['b'],metadata['domain_size'])
        a=tuple((c,int(v,16)) for c,v in row['a'])
        b=tuple((c,int(v,16)) for c,v in row['b'])
        raw[index]=(a,b)
        normalized[index]=tuple(canonical((0 if c==copy else c,v) for c,v in lc) for lc in (a,b))
    def observed(value):
        return checked['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    products={};templates={}
    for entry in extracted['products']:
        if entry['role'] in products:
            raise relation.RelationError('duplicate ownership quotient product role')
        products[entry['role']]=entry['rows']
    for entry in extracted['templates']:
        for role in entry['roles']:
            if role in templates:
                raise relation.RelationError('duplicate ownership quotient template role')
            templates[role]=entry['row']
    chosen=list(range(2)) if include_precompute else []
    chosen+=list(range(2+3*window_offset,5+3*window_offset))
    certificates=[];used=set()
    for index in chosen:
        quotient=checked['quotients'][index]
        for axis in range(2):
            numerator,denominator,q=map(observed,(quotient[axis],quotient[axis+2],quotient[axis+4]))
            role=f'quotient.{index}.{axis}'
            folded=next(((lc,other) for lc,other in ((denominator,q),(q,denominator))
                         if not lc or len(lc)==1 and lc[0][0]==0),None)
            certificate={'role':role,'numerator':numerator,'denominator':denominator,'quotient':q}
            if folded:
                constant,other=folded;coefficient=constant[0][1] if constant else 0
                output=canonical((c,v*coefficient) for c,v in other)
                equation=combine(output,numerator,-1)
                indices=[] if not equation else [templates.get(role+'.assertion')]
                if equation and (None in indices or normalized[indices[0]] not in
                                 ((equation,()),(canonical((c,-v) for c,v in equation),()))):
                    raise relation.RelationError('ownership folded quotient assertion mismatch')
                certificate.update(kind='folded',coefficient=coefficient,output=output,rows=indices)
            elif q==denominator:
                indices=products.get(role,[])
                if len(indices)!=2 or any(i not in normalized for i in indices):
                    raise relation.RelationError('ownership quotient needs square and assertion')
                square,assertion=(normalized[i] for i in indices)
                if square[0]!=q:
                    raise relation.RelationError('ownership quotient square operand mismatch')
                output=square[1];equation=combine(output,numerator,-1)
                if assertion not in ((equation,()),(canonical((c,-v) for c,v in equation),())):
                    raise relation.RelationError('ownership quotient materialized assertion mismatch')
                certificate.update(kind='square',output=output,rows=indices)
            else:
                indices=products.get(role,[])
                if len(indices)!=3 or any(i not in normalized for i in indices):
                    raise relation.RelationError('ownership quotient needs product pair and assertion')
                minus,plus,assertion=(normalized[i] for i in indices)
                difference=combine(q,denominator,-1)
                if minus[0] not in (difference,canonical((c,-v) for c,v in difference)) or plus[0]!=combine(q,denominator):
                    raise relation.RelationError('ownership quotient product operands mismatch')
                output=canonical((c,v*pow(4,-1,p)) for c,v in combine(plus[1],minus[1],-1))
                equation=combine(output,numerator,-1)
                if assertion not in ((equation,()),(canonical((c,-v) for c,v in equation),())):
                    raise relation.RelationError('ownership quotient materialized assertion mismatch')
                certificate.update(kind='product',output=output,auxiliary=minus[1],rows=indices,
                                   swapped=minus[0]!=difference)
            used.update(indices);certificates.append(certificate)
    copy_row=templates.get('constant-copy')
    if copy_row is None or raw[copy_row]!=(canonical([(0,1),(copy,p-1)]),()):
        raise relation.RelationError('ownership quotient constant link mismatch')
    used.add(copy_row)
    return {'outline':copy,'rows':{i:raw[i] for i in sorted(used)},'certificates':certificates}


def first_window_controls(checked, extracted):
    """Actual first-window arithmetic omission, excluding the rest of Transfer."""
    if checked['metadata']['window_start'] != 0:
        raise relation.RelationError('first ownership control requires global window zero')
    cones=cone_certificates(checked,extracted,0)
    quotients=quotient_certificates(checked,extracted,0)
    rows={**cones['rows'],**quotients['rows']};p=relation.MODULUS
    def evaluate(lc,rho):return sum(v*rho.get(c,0) for c,v in lc)%p
    def solve(lc,value,rho):
        missing=[(c,v) for c,v in lc if c not in rho]
        if len(missing)>1:raise relation.RelationError('ownership control ambiguous LC assignment')
        if missing:
            c,v=missing[0];rho[c]=(value-evaluate(lc,rho))*pow(v,-1,p)%p
        if evaluate(lc,rho)!=value%p:raise relation.RelationError('ownership control LC conflict')
    d=-10240*pow(10241,-1,p)%p
    def add(a,b):
        x,y=a;u,v=b;t=d*x*y*u*v%p
        return ((x*v+y*u)*pow((1+t)%p,-1,p)%p,
                (x*u+y*v)*pow((1-t)%p,-1,p)%p)
    q=(3,26155723652191673091881779851507865815856437797311909079256717375290769542325)
    base=q
    for _ in range(3):base=add(base,base)
    twice=add(base,base);triple=add(twice,base)
    if (base[1]**2-base[0]**2-1-d*base[0]**2*base[1]**2)%p or base[0]==0:
        raise relation.RelationError('ownership control base curve/nonidentity failure')
    def observed(value):
        return checked['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    final=quotients['certificates'][-2]
    if final['role']!='quotient.4.0' or final['kind']!='folded' or len(final['rows'])!=1:
        raise relation.RelationError('ownership first add-x boundary changed')
    omitted=final['rows'][0];cases=[]
    for name,output,removed in [('positive',(0,1),None),('missing-first-add-x',(3,1),omitted)]:
        rho={0:1,checked['metadata']['constant_copy']:1}
        for role,point in [('base',base),('twice',twice),('triple',triple)]:
            for value,n in zip(checked['points'][role],point):solve(observed(value),n,rho)
        for handle in checked['bits'][250:252]:solve(checked['derived'][handle],0,rho)
        window=checked['windows'][0]
        for point,values in zip(window,[(0,1),(0,1),(0,1),(0,1),output]):
            if point == window[3]:continue  # Selector LCs are computed below.
            for value,n in zip(point,values):solve(observed(value),n,rho)
        ordered_cones=sorted(cones['cones'],key=lambda c:(0 if int(c['role'][7:])<8 else
                                                       1 if int(c['role'][7:])>=20 else 2,
                                                       int(c['role'][7:])))
        for cone in ordered_cones:
            for identity in cone['ordered']:
                node=cone['source'][identity];lc=cones['observations'][identity][1]
                if identity in cone['inputs']:continue
                if node['kind']=='constant':value=node['value']
                else:
                    a=evaluate(cones['observations'][node['left']][1],rho)
                    b=evaluate(cones['observations'][node['right']][1],rho)
                    value=a+b if node['kind']=='add' else a*b
                solve(lc,value,rho)
                certificate=cone['certificates'][identity]
                if certificate['kind']=='product':
                    index=certificate['rows'][0];a,b=rows[index]
                    solve(b,evaluate(a,rho)**2,rho)
        for certificate in quotients['certificates']:
            if certificate['kind']=='folded':continue
            solve(certificate['output'],evaluate(certificate['quotient'],rho)*evaluate(certificate['denominator'],rho),rho)
            if certificate['kind']=='product':
                a,b=rows[certificate['rows'][0]];solve(b,evaluate(a,rho)**2,rho)
        rejected=sorted(i for i,(a,b) in rows.items() if evaluate(a,rho)**2%p!=evaluate(b,rho))
        if rejected!=([] if removed is None else [removed]):
            raise relation.RelationError('ownership control intended row failure not observed')
        actual=tuple(evaluate(observed(v),rho) for v in window[4])
        selector=tuple(evaluate(observed(v),rho) for v in window[3])
        if selector!=(0,1) or any(evaluate(checked['derived'][h],rho)!=0 for h in checked['bits'][250:252]):
            raise relation.RelationError('ownership control tested digit/selector predicate not observed')
        if (removed is None and actual!=(0,1)) or (removed is not None and actual==(0,1)):
            raise relation.RelationError('ownership control output predicate not observed')
        cases.append({'name':name,'assignment':sorted(rho.items()),'omitted_original_row':removed,
                      'original_rejected_rows':rejected,'retained_selected_rows_satisfied':True,
                      'actual_output':actual,'expected_output':(0,1)})
    return {'scope':f'actual {len(rows)}-row first-window arithmetic control; nonzero IVK and other Transfer constraints excluded',
            'cases':cases}


def endpoint_controls(chunks, extractions):
    """Evaluate the complete selected ownership loop and one endpoint omission.

    This uses scalar one and a nonidentity subgroup base. It does not claim
    satisfaction of the IVK hash/reduction or any other Transfer component.
    """
    if not isinstance(chunks, list) or len(chunks) != 8:
        raise relation.RelationError('ownership endpoint requires eight complete chunks')
    join_chunks(chunks)
    if not isinstance(extractions, list) or len(extractions) != len(chunks):
        raise relation.RelationError('ownership endpoint extraction count')
    p = relation.MODULUS
    rows, derived, nodes = {}, {}, {}
    endpoint = None
    for chunk, extracted in zip(chunks, extractions):
        identity = extracted.get('identity', {})
        if (identity.get('relation_digest') != chunk['metadata']['relation_digest'] or
                identity.get('stored_rows') != chunk['metadata']['full_rows'] or
                identity.get('domain_size') != chunk['metadata']['domain_size']):
            raise relation.RelationError('ownership endpoint extraction identity/shape')
        derived.update(chunk['derived']); nodes.update(chunk['nodes'])
        for row in extracted['selected_rows']:
            index = relation.natural(row['row'], chunk['metadata']['full_rows'])
            for terms in (row['a'], row['b']):
                relation.terms(terms, chunk['metadata']['domain_size'])
            value = tuple(tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
            if index in rows and rows[index] != value:
                raise relation.RelationError('ownership endpoint overlapping row mismatch')
            rows[index] = value
        for template in extracted['templates']:
            if 'target.0' in template['roles']:
                if endpoint is not None and endpoint != template['row']:
                    raise relation.RelationError('ownership endpoint duplicated target row')
                endpoint = template['row']
    if endpoint not in rows:
        raise relation.RelationError('ownership endpoint missing final target-x row')
    copy = chunks[0]['metadata']['constant_copy']
    d = -10240 * pow(10241, -1, p) % p

    def evaluate(lc, rho):
        if any(c not in rho for c, _ in lc):
            raise relation.RelationError('ownership endpoint unassigned LC operand')
        return sum(v * rho[c] for c, v in lc) % p

    def solve(lc, value, rho):
        missing = [(c, v) for c, v in lc if c not in rho]
        if len(missing) > 1:
            raise relation.RelationError('ownership endpoint ambiguous LC assignment')
        if missing:
            c, v = missing[0]
            known = sum(v * rho[c] for c, v in lc if c in rho) % p
            rho[c] = (value - known) * pow(v, -1, p) % p
        if evaluate(lc, rho) != value % p:
            raise relation.RelationError('ownership endpoint conflicting LC assignment')

    def add(a, b):
        x, y = a; u, v = b
        delta = d * x * y * u * v % p
        return ((x * v + y * u) * pow((1 + delta) % p, -1, p) % p,
                (x * u + y * v) * pow((1 - delta) % p, -1, p) % p)

    def multiply(n, point):
        result = (0, 1)
        while n:
            if n & 1: result = add(result, point)
            point = add(point, point); n >>= 1
        return result

    q = (3, 26155723652191673091881779851507865815856437797311909079256717375290769542325)
    base = multiply(8, q); twice = add(base, base); triple = add(twice, base)
    order = 6554484396890773809930967563523245729705921265872317281365359162392183254199
    # This is the concrete Edwards group calculation for the scoped controls,
    # separate from the kernel's explicit StandardCurveModel contract.
    if base[0] == 0 or multiply(order, base) != (0, 1):
        raise relation.RelationError('ownership endpoint base subgroup/nonidentity')
    cases = []
    for name, target, omitted in [('positive', base, None),
                                  ('missing-target-x', ((-base[0]) % p, base[1]), endpoint)]:
        values = {}
        expected_nodes = {}

        def assign(observed, value):
            value %= p
            if observed[0] == 'native':
                if observed[1] != value:
                    raise relation.RelationError('ownership endpoint native point mismatch')
                return
            handle = observed[1]
            destination = expected_nodes if handle[0] == 2 else values
            if handle in destination and destination[handle] != value:
                raise relation.RelationError('ownership endpoint point role conflict')
            destination[handle] = value

        for chunk in chunks:
            for role, point in [('base', base), ('twice', twice), ('triple', triple),
                                ('output', base), ('target', target)]:
                for observed, value in zip(chunk['points'][role], point): assign(observed, value)
            for index, handle in enumerate(chunk['bits']):
                assign(('source', handle), 1 if index == 0 else 0)
            current = (0, 1)
            # Every preceding digit is zero for scalar one, so each chunk starts
            # at identity; only the final global window selects the base.
            for offset, window in enumerate(chunk['windows']):
                index = chunk['metadata']['window_start'] + offset
                first = add(current, current); second = add(first, first)
                selected = base if index == 125 else (0, 1)
                output = add(second, selected)
                for observed_point, point in zip(window, [current, first, second, selected, output]):
                    for observed, value in zip(observed_point, point): assign(observed, value)
                current = output
        rho = {0: 1, copy: 1}
        for handle in sorted(derived):
            if handle[0] == 0:
                lc = derived[handle]
                values[handle] = sum(v for c, v in lc if c == 0) % p
            elif handle[0] == 1:
                if handle not in values:
                    raise relation.RelationError('ownership endpoint unassigned source witness')
            else:
                multiply_node, left, right = nodes[handle]
                values[handle] = ((values[left] * values[right]) if multiply_node else
                                  (values[left] + values[right])) % p
                if handle in expected_nodes and values[handle] != expected_nodes[handle]:
                    raise relation.RelationError('ownership endpoint selector/source value mismatch')
            solve(derived[handle], values[handle], rho)
        for index, (a, b) in sorted(rows.items()):
            if any(c not in rho for c, _ in b): solve(b, evaluate(a, rho) ** 2 % p, rho)
        rejected = sorted(index for index, (a, b) in rows.items()
                          if evaluate(a, rho) ** 2 % p != evaluate(b, rho))
        if rejected != ([] if omitted is None else [omitted]):
            raise relation.RelationError('ownership endpoint intended row failure not observed')
        actual = tuple(evaluate(chunks[-1]['derived'][observed[1]], rho)
                       for observed in chunks[-1]['points']['output'])
        actual_target = tuple(evaluate(chunks[-1]['derived'][observed[1]], rho)
                              for observed in chunks[-1]['points']['target'])
        scalar = sum(evaluate(derived[handle], rho) * (1 << index)
                     for index, handle in enumerate(chunks[0]['bits']))
        x, y = actual_target
        if (y * y - x * x - 1 - d * x * x * y * y) % p or x == 0 or multiply(order, actual_target) != (0, 1):
            raise relation.RelationError('ownership endpoint target group predicate not observed')
        if scalar != 1 or actual != multiply(scalar, base) or (actual == actual_target) != (omitted is None):
            raise relation.RelationError('ownership endpoint violated ownership predicate not observed')
        cases.append({'name': name, 'assignment': sorted(rho.items()),
                      'omitted_original_row': omitted, 'original_rejected_rows': rejected,
                      'retained_selected_rows_satisfied': True, 'scalar': scalar,
                      'actual_output': actual, 'actual_target': actual_target,
                      'target_on_curve_nonidentity_subgroup': True})
    return {'scope': f'actual {len(rows)}-row ownership-loop controls; IVK hash/reduction and other Transfer constraints excluded',
            'cases': cases}


def generate_quotient_boundaries(selected, metadata_hash, relation_digest,
                                 namespace='RuntimeOwnershipQuotients'):
    """Emit arithmetic Div equations; no denominator nonzero premise is hidden."""
    from .generate_hash_round import linear, signed, _signature_audits
    if any(not isinstance(value,str) or not re.fullmatch('[0-9a-f]{64}',value)
           for value in (metadata_hash,relation_digest)):
        raise relation.RelationError('ownership quotient generator identity')
    if not isinstance(namespace,str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',namespace):
        raise relation.RelationError('ownership quotient generator namespace')
    copy=selected['outline']
    out=[f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 500000
namespace ShielddSecurity.{namespace}
-- Metadata SHA256: {metadata_hash}; relation digest: {relation_digest}
-- Selected original row indices: {list(selected['rows'])}
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := [
''']
    out.append(',\n'.join('⟨'+linear(a)+', '+linear(b)+'⟩' for a,b in selected['rows'].values()))
    out.append(f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0, 1), ({copy}, -1)], []⟩ = true := by decide
''')
    for index,c in enumerate(selected['certificates']):
        prefix='equation'+str(index)
        for role in ('quotient','denominator','numerator','output'):
            out.append(f'def {prefix}_{role} : Linear := {linear(c[role])}\n')
        q,d,n,o=(prefix+'_'+role for role in ('quotient','denominator','numerator','output'))
        out.append(f'''theorem {prefix}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho {q} * eval rho {d} = eval rho {n} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product : eval rho {o} = eval rho {q} * eval rho {d} := by
''')
        if c['kind']=='product':
            left,right=(d,q) if c['swapped'] else (q,d)
            out.append(f'''    have checked := Compiler.checked_product_sound rho rows {left} {right} {o}
      ({linear(c['auxiliary'])}) four normalized (by decide) (by decide)
    simpa only [mul_comm] using checked
''')
        elif c['kind']=='square':
            out.append(f'''    have checked := Compiler.checked_square_sound rho rows {q} {o} normalized (by decide)
    have same := Compiler.canonical_equal rho {q} {d} (by decide)
    simpa only [same] using checked
''')
        else:
            constant,other=(d,q) if not c['denominator'] or all(col==0 for col,_ in c['denominator']) else (q,d)
            coefficient=signed(c['coefficient'])
            out.append(f'''    have fixed : eval rho {constant} = (({coefficient} : Int) : F) := by
      have checked := Compiler.canonical_equal rho {constant} [(0, ({coefficient} : Int))] (by decide)
      simpa [eval, one] using checked
    have folded := Compiler.canonical_equal rho {o} (scaleLinear ({coefficient} : Int) {other}) (by decide)
    rw [eval_scale] at folded
    rw [fixed]
    simpa only [mul_comm] using folded
''')
        equation=combine(c['output'],c['numerator'],-1)
        if not equation:
            out.append(f'  have assertion := Compiler.canonical_equal rho {o} {n} (by decide)\n')
        else:
            assertion_index=c['rows'][-1]
            a=canonical((0 if col==copy else col,v) for col,v in selected['rows'][assertion_index][0])
            left,right=(o,n) if a==equation else (n,o)
            out.append(f'  have checked := Compiler.checked_assertion_sound rho rows {left} {right} normalized (by decide)\n')
            out.append('  have assertion := checked'+('' if left==o else '.symm')+'\n')
        out.append('  exact product.symm.trans assertion\n\n#print axioms '+prefix+'_sound\n')
    out.append('#print axioms constantLink\nend ShielddSecurity.'+namespace+'\n')
    return _signature_audits(''.join(out))


def window_renaming(template, template_rows, target, target_rows,
                    template_offset=0, target_offset=0, *, include_precompute=False):
    """Checked physical-column substitution for one arithmetic window.

    No claim follows from the mapping alone: the kernel must transport row
    satisfaction and every named input/output role under this substitution.
    """
    for key in ('relation_digest','domain_size','full_rows','constant_copy'):
        if template['metadata'][key]!=target['metadata'][key]:
            raise relation.RelationError('ownership renaming relation/shape mismatch')
    first = (template['metadata']['window_start']+template_offset,
             target['metadata']['window_start']+target_offset)
    if type(include_precompute) is not bool or (min(first)<=0 and not (first==(0,0) and include_precompute)):
        raise relation.RelationError('ownership renaming requires noninitial windows or paired initial precompute')
    tc=cone_certificates(template,template_rows,template_offset,include_precompute)
    ac=cone_certificates(target,target_rows,target_offset,include_precompute)
    tq=quotient_certificates(template,template_rows,template_offset,include_precompute)
    aq=quotient_certificates(target,target_rows,target_offset,include_precompute)
    tm=match_formulas(template)['cones'][8+14*template_offset:22+14*template_offset]
    am=match_formulas(target)['cones'][8+14*target_offset:22+14*target_offset]
    if include_precompute:
        tm=match_formulas(template)['cones'][:8]+tm
        am=match_formulas(target)['cones'][:8]+am
    lc_pairs=[];row_pairs=[]
    mapping={0:0,template['metadata']['constant_copy']:target['metadata']['constant_copy']}
    for tcone,acone,tmatch,amatch in zip(tc['cones'],ac['cones'],tm,am):
        if tmatch['graph']!=amatch['graph']:
            raise relation.RelationError('ownership renaming formula template mismatch')
        tp,ap=dict(tmatch['pairs']),dict(amatch['pairs'])
        if set(tp)!=set(ap):raise relation.RelationError('ownership renaming source correspondence mismatch')
        for identity in sorted(tp):
            tname,aname=tp[identity],ap[identity]
            lc_pairs.append((tc['observations'][tname][1],ac['observations'][aname][1]))
            tcert,acert=tcone['certificates'][tname],acone['certificates'][aname]
            if tcert['kind']!=acert['kind'] or len(tcert.get('rows',[]))!=len(acert.get('rows',[])):
                raise relation.RelationError('ownership renaming compiler-case mismatch')
            row_pairs.extend(zip(tcert.get('rows',[]),acert.get('rows',[])))
        for tname,aname in zip(tcone['inputs'],acone['inputs']):
            lc_pairs.append((tc['observations'][tname][1],ac['observations'][aname][1]))
    for tcert,acert in zip(tq['certificates'],aq['certificates']):
        if tcert['kind']!=acert['kind'] or len(tcert['rows'])!=len(acert['rows']):
            raise relation.RelationError('ownership renaming quotient-case mismatch')
        for role in ('numerator','denominator','quotient','output'):
            lc_pairs.append((tcert[role],acert[role]))
        row_pairs.extend(zip(tcert['rows'],acert['rows']))
    tr={**tc['rows'],**tq['rows']};ar={**ac['rows'],**aq['rows']}
    row_pairs.append((next(i for i,row in tr.items() if row==(canonical([(0,1),(tc['outline'],-1)]),())),
                      next(i for i,row in ar.items() if row==(canonical([(0,1),(ac['outline'],-1)]),()))))
    for ti,ai in row_pairs:
        for a,b in zip(tr[ti],ar[ai]):lc_pairs.append((a,b))
    # Infer only single remaining coordinates; never guess a permutation of
    # equal-coefficient terms. Actual equality below combines any collisions.
    pending=lc_pairs[:]
    for _ in range(256):
        progress=False;remaining=[]
        for left,right in pending:
            known=canonical((mapping[c],v) for c,v in left if c in mapping)
            residual=combine(right,known,-1)
            missing=[(c,v) for c,v in left if c not in mapping]
            if not missing:
                if residual:raise relation.RelationError('ownership renaming LC equality mismatch')
            elif len(missing)==len(residual)==1 and missing[0][1]==residual[0][1]:
                mapping[missing[0][0]]=residual[0][0];progress=True
            else:remaining.append((left,right))
        pending=remaining
        if not pending:break
        if not progress:raise relation.RelationError('ownership renaming ambiguous column substitution')
    if pending:raise relation.RelationError('ownership renaming finite inference bound')
    row_targets={}
    for ti,ai in row_pairs:
        if ti in row_targets and row_targets[ti]!=ai:
            raise relation.RelationError('ownership renaming row role conflict')
        row_targets[ti]=ai
        renamed=tuple(canonical((mapping[c],v) for c,v in lc) for lc in tr[ti])
        if renamed!=ar[ai]:raise relation.RelationError('ownership renaming actual row mismatch')
    if set(row_targets)!=set(tr):raise relation.RelationError('ownership renaming omitted template row')
    return {'columns':sorted(mapping.items()),'row_targets':sorted(row_targets.items()),
            'template_rows':tr,'actual_rows':ar,'template_offset':template_offset,'target_offset':target_offset,
            'scope':'checked source/LC/actual-row substitution only; kernel role/satisfaction transport pending'}


def chunk_renaming(template, template_rows, target, target_rows):
    """Complete bounded trace substitution; mappings alone carry no proof."""
    tm,am=template['metadata'],target['metadata']
    if (tm['window_start'],tm['window_count'])!=(am['window_start'],am['window_count']):
        raise relation.RelationError('trace substitution chunk interval mismatch')
    columns={};windows=[]
    for offset in range(tm['window_count']):
        selected=window_renaming(template,template_rows,target,target_rows,offset,offset,
                                include_precompute=tm['window_start']+offset==0)
        for source,actual in selected['columns']:
            if source in columns and columns[source]!=actual:
                raise relation.RelationError('trace substitution inconsistent column images')
            columns[source]=actual
        windows.append(selected)
    low=2*(126-tm['window_start']-tm['window_count'])
    high=2*(126-tm['window_start'])
    for index in range(low,high):
        source=template['derived'][template['bits'][index]]
        actual=target['derived'][target['bits'][index]]
        if canonical((columns[column],coefficient) for column,coefficient in source)!=actual:
            raise relation.RelationError('trace substitution bit role mismatch')
        if template['bits'][index]!=target['bits'][index] or source!=actual:
            raise relation.RelationError('trace substitution requires same accepted IVK bits')
    for selected in windows:
        for source,row in selected['template_rows'].items():
            actual_id=dict(selected['row_targets'])[source]
            if tuple(canonical((columns[column],value) for column,value in lc) for lc in row)!=selected['actual_rows'][actual_id]:
                raise relation.RelationError('trace merged substitution row mismatch')
    return {'columns':sorted(columns.items()),'windows':windows,'window_start':tm['window_start'],
            'window_count':tm['window_count'],
            'scope':'complete bounded arithmetic/bit role substitution; kernel trace transport pending'}


def generate_trace_substitution(template, template_rows, target, target_rows):
    """Transport a checked bounded Owner trace onto actual RNK loop rows.

    Each small window block is checked separately. Role equalities transport
    the same assignment, including decoded bits; no group result is assumed.
    """
    from .generate_hash_round import linear, _signature_audits
    selected=chunk_renaming(template,template_rows,target,target_rows)
    start,count=selected['window_start'],selected['window_count']
    source=f'ShielddSecurity.RuntimeOwnershipTrace{start:03d}'
    name=f'RuntimeRnkTrace{start:03d}'
    copy=target['metadata']['constant_copy']
    ranges=[]
    for source_column,actual_column in selected['columns']:
        delta=actual_column-source_column
        if not delta:continue
        if ranges and ranges[-1][1]+1==source_column and ranges[-1][2]==delta:
            ranges[-1]=(ranges[-1][0],source_column,delta)
        else:ranges.append((source_column,source_column,delta))
    if len(ranges)>64:raise relation.RelationError('trace translation representation exceeds64 ranges')
    column_expression='column'
    for first,last,delta in reversed(ranges):
        translated=f'column + {delta}' if delta>=0 else f'column - {-delta}'
        column_expression=f'if {first} ≤ column ∧ column ≤ {last} then {translated} else ({column_expression})'
    for source_column,actual_column in selected['columns']:
        translated=next((source_column+delta for first,last,delta in ranges if first<=source_column<=last),source_column)
        if translated!=actual_column:raise relation.RelationError('trace compressed column representation mismatch')
    def lc(value):
        return target['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    def rows_literal(rows):
        return '['+',\n'.join('⟨'+linear(a)+', '+linear(b)+'⟩' for a,b in rows)+']'
    out=[f'''import ShielddSecurity.RuntimeOwnershipTrace{start:03d}
import ShielddSecurity.RowRenaming
set_option maxHeartbeats 500000
namespace ShielddSecurity.{name}
def modulus : Nat := {relation.MODULUS}
def coefficientD : Int := {source}.coefficientD
def columnPairs : List (Nat × Nat) := {selected['columns']}
def columns (column : Nat) : Nat :=
  {column_expression}
theorem columns_zero : columns 0 = 0 := by decide
''']
    for offset,window in enumerate(selected['windows']):
        rows=[window['actual_rows'][i] for i in sorted(window['actual_rows'])]
        out.append(f'def rows{offset} : List Row := {rows_literal(rows)}\n')
    low=2*(126-start-count);high=2*(126-start)
    bit_rows=[(target['derived'][target['bits'][i]],target['derived'][target['bits'][i]])
              for i in range(low,high)]
    out.append(f'def bitRows : List Row := {rows_literal(bit_rows)}\n')
    blocks=[f'rows{i}' for i in range(count)]+['bitRows']
    out.append(f'''def blocks : List (List Row) := [{', '.join(blocks)}]
def rawRows : List Row := blocks.flatten
private theorem block_included (block : List Row) (member : block ∈ blocks) :
    ∀ row ∈ block, row ∈ rawRows := by
  intro row inBlock
  exact List.mem_flatten.mpr ⟨block, member, inBlock⟩
''')
    def membership(index):
        term='List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(index):term='List.mem_cons.mpr (Or.inr ('+term+'))'
        return 'by exact '+term
    for offset in range(count):
        module=f'ShielddSecurity.RuntimeOwnershipWindow{start+offset:03d}'
        out.append(f'''private theorem window{offset}_satisfied {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => rho (columns column)) {module}.rawRows := by
  have included := block_included rows{offset} ({membership(offset)})
  exact RowRenaming.checked_rows rho columns {module}.rawRows rows{offset}
    (by decide) (fun row member => satisfied row (included row member))
''')
    out.append(f'''private theorem source_satisfied {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => rho (columns column)) {source}.rawRows := by
  have bitIncluded := block_included bitRows ({membership(count)})
  have bitSatisfied := RowRenaming.checked_rows rho columns {source}.bitRows bitRows
    (by decide) (fun row member => satisfied row (bitIncluded row member))
  intro row member
  rcases List.mem_append.mp member with windowMember | bitMember
  · obtain ⟨block, blockMember, rowMember⟩ := List.mem_flatten.mp windowMember
    simp only [{source}.windowRows, List.mem_cons, List.not_mem_nil, or_false] at blockMember
    rcases blockMember with { ' | '.join('h'+str(i) for i in range(count)) }
''')
    for offset in range(count):
        out.append(f'    · subst block; exact window{offset}_satisfied rho satisfied row rowMember\n')
    out.append('  · exact bitSatisfied row bitMember\n')
    # Actual point definitions and checked transport of the four shared roles.
    role_values={'base':target['points']['base'],'twice':target['points']['twice'],
                 'triple':target['points']['triple'],'input':target['windows'][0][0]}
    for role,values in role_values.items():
        out.append(f'def {role} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(lc(values[0]))}, eval rho {linear(lc(values[1]))}⟩\n')
        owner_values=(template['windows'][0][0] if role=='input' else template['points'][role])
        def owner_lc(value):
            return template['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
        out.append(f'''theorem {role}_role {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    {source}.{role} (fun column => rho (columns column)) = {role} rho := by
  apply congrArg₂ Group.Point.mk
''')
        for axis in range(2):
            a,b=linear(owner_lc(owner_values[axis])),linear(lc(values[axis]))
            out.append(f'  · change eval (fun column => rho (columns column)) {a} = eval rho {b}\n    exact RowRenaming.checked_linear rho columns {a} {b} (by decide)\n')
    for offset,window in enumerate(target['windows']):
        module=f'ShielddSecurity.RuntimeOwnershipWindow{start+offset:03d}'
        bit_index=2*(125-start-offset)
        bit_lcs=[target['derived'][target['bits'][bit_index+i]] for i in range(2)]
        point_roles=('first','second','output')
        for role,position in zip(point_roles,(1,2,4)):
            values=window[position]
            out.append(f'def window{offset}_{role} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(lc(values[0]))}, eval rho {linear(lc(values[1]))}⟩\n')
        out.append(f'''noncomputable def window{offset} {{F : Type}} [Field F] (rho : Nat → F) : TransferOwnership.WindowWitness F :=
  ⟨ScalarBits.decodeBit rho {linear(bit_lcs[0])}, ScalarBits.decodeBit rho {linear(bit_lcs[1])},
    window{offset}_first rho, window{offset}_second rho, window{offset}_output rho⟩
theorem window{offset}_role {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    {source}.window{offset} (fun column => rho (columns column)) = window{offset} rho := by
''')
        for axis,role in enumerate(('low','high')):
            out.append(f'''  have {role}Value := RowRenaming.checked_linear rho columns {module}.{role} {linear(bit_lcs[axis])} (by decide)
  have {role}Role : ScalarBits.decodeBit (fun column => rho (columns column)) {module}.{role} = ScalarBits.decodeBit rho {linear(bit_lcs[axis])} := by
    classical
    exact congrArg (fun value : F => decide (value = 1)) {role}Value
''')
        for role,position,source_role in zip(point_roles,(1,2,4),('first','second','result')):
            out.append(f'  have {role}Role : {module}.{source_role} (fun column => rho (columns column)) = window{offset}_{role} rho := by\n    apply congrArg₂ Group.Point.mk\n')
            for axis in range(2):
                value=template['windows'][offset][position][axis]
                a=linear(owner_lc(value));b=linear(lc(window[position][axis]))
                out.append(f'    · change eval (fun column => rho (columns column)) {a} = eval rho {b}\n      exact RowRenaming.checked_linear rho columns {a} {b} (by decide)\n')
        out.append(f'  simp only [{source}.window{offset}, window{offset}, lowRole, highRole, firstRole, secondRole, outputRole]\n')
    out.append(f'''noncomputable def windows {{F : Type}} [Field F] (rho : Nat → F) := [{', '.join('window'+str(i)+' rho' for i in range(count))}]
theorem windows_role {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    {source}.windows (fun column => rho (columns column)) = windows rho := by
  simp only [{source}.windows, windows, {', '.join('window'+str(i)+'_role' for i in range(count))}]
theorem actual_trace_equations {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.TraceEquations (coefficientD : F) (base rho) (twice rho) (triple rho)
      (input rho) (windows rho) := by
  have zero : rho (columns 0) = 1 := by rw [columns_zero]; exact one
  have equations := {source}.actual_trace_equations (fun column => rho (columns column)) zero four (source_satisfied rho satisfied)
  rw [base_role, twice_role, triple_role, input_role, windows_role] at equations
  exact equations
''')
    names=['columns_zero']+[role+'_role' for role in role_values]+['window'+str(i)+'_role' for i in range(count)]+['windows_role','actual_trace_equations']
    out.extend('#print axioms '+name+'\n' for name in names)
    out.append('end ShielddSecurity.'+name+'\n')
    return _signature_audits(''.join(out))


def generate_rnk_precompute_bridge():
    """Derive the shared RNK precomputations from the first actual row block."""
    from .generate_hash_round import _signature_audits
    source='''import ShielddSecurity.RuntimeRnkTrace000
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeRnkPrecompute
def modulus : Nat := ShielddSecurity.RuntimeRnkTrace000.modulus
def rawRows : List Row := ShielddSecurity.RuntimeRnkTrace000.rawRows
theorem actual_precompute {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.DoubleEquations (ShielddSecurity.RuntimeRnkTrace000.base rho)
      (ShielddSecurity.RuntimeRnkTrace000.twice rho) ∧
    TransferOwnership.AddEquations (ShielddSecurity.RuntimeRnkTrace000.coefficientD : F)
      (ShielddSecurity.RuntimeRnkTrace000.twice rho) (ShielddSecurity.RuntimeRnkTrace000.base rho)
      (ShielddSecurity.RuntimeRnkTrace000.triple rho) := by
  have block : Satisfies rho ShielddSecurity.RuntimeRnkTrace000.rows0 := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr
      ⟨ShielddSecurity.RuntimeRnkTrace000.rows0, List.mem_cons.mpr (Or.inl rfl), member⟩)
  have source := RowRenaming.checked_rows rho ShielddSecurity.RuntimeRnkTrace000.columns
    ShielddSecurity.RuntimeOwnershipWindow000.rawRows ShielddSecurity.RuntimeRnkTrace000.rows0
    (by decide) block
  have zero : rho (ShielddSecurity.RuntimeRnkTrace000.columns 0) = 1 := by
    rw [ShielddSecurity.RuntimeRnkTrace000.columns_zero]; exact one
  have equations := ShielddSecurity.RuntimeOwnershipWindow000.arithmetic_window
    (fun column => rho (ShielddSecurity.RuntimeRnkTrace000.columns column)) zero four source
  have doubled := equations.1
  have added := equations.2.1
  change TransferOwnership.DoubleEquations
    (ShielddSecurity.RuntimeOwnershipTrace000.base (fun column => rho (ShielddSecurity.RuntimeRnkTrace000.columns column)))
    (ShielddSecurity.RuntimeOwnershipTrace000.twice (fun column => rho (ShielddSecurity.RuntimeRnkTrace000.columns column))) at doubled
  change TransferOwnership.AddEquations (ShielddSecurity.RuntimeRnkTrace000.coefficientD : F)
    (ShielddSecurity.RuntimeOwnershipTrace000.twice (fun column => rho (ShielddSecurity.RuntimeRnkTrace000.columns column)))
    (ShielddSecurity.RuntimeOwnershipTrace000.base (fun column => rho (ShielddSecurity.RuntimeRnkTrace000.columns column)))
    (ShielddSecurity.RuntimeOwnershipTrace000.triple (fun column => rho (ShielddSecurity.RuntimeRnkTrace000.columns column))) at added
  rw [ShielddSecurity.RuntimeRnkTrace000.base_role, ShielddSecurity.RuntimeRnkTrace000.twice_role] at doubled
  rw [ShielddSecurity.RuntimeRnkTrace000.twice_role, ShielddSecurity.RuntimeRnkTrace000.base_role,
    ShielddSecurity.RuntimeRnkTrace000.triple_role] at added
  exact ⟨doubled, added⟩
#print axioms actual_precompute
end ShielddSecurity.RuntimeRnkPrecompute
'''
    return _signature_audits(source)


def generate_renamed_window(template, template_rows, target, target_rows,
        template_offset=0,target_offset=0,template_module='RuntimeOwnershipWindow016',
        template_namespace='RuntimeOwnershipWindow016',namespace='RuntimeOwnershipWindow017'):
    """Reuse a kernel-checked noninitial arithmetic template with exact roles."""
    from .generate_hash_round import linear,signed,_signature_audits
    for name in (template_module,template_namespace,namespace):
        if not isinstance(name,str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',name):
            raise relation.RelationError('ownership renaming module name')
    selected=window_renaming(template,template_rows,target,target_rows,template_offset,target_offset)
    T='ShielddSecurity.'+template_namespace
    source=f'''import ShielddSecurity.{template_module}
import ShielddSecurity.RowRenaming
set_option maxHeartbeats 500000
namespace ShielddSecurity.{namespace}
def columnPairs : List (Nat × Nat) := {selected['columns']}
def columns (column : Nat) : Nat :=
  ((columnPairs.find? (fun pair => pair.1 = column)).map Prod.snd).getD column
def modulus : Nat := {relation.MODULUS}
def coefficientD : Int := {signed(-10240*pow(10241,-1,relation.MODULUS)%relation.MODULUS)}
def originalRows : List Nat := {sorted(selected['actual_rows'])}
def rawRows : List Row := [
'''+',\n'.join('  ⟨'+linear(a)+', '+linear(b)+'⟩' for _,(a,b) in sorted(selected['actual_rows'].items()))+f''']
theorem columns_zero : columns 0 = 0 := by decide
theorem rows_checked : {T}.rawRows.all
    (fun item => Compiler.checkRow modulus rawRows (RowRenaming.row columns item)) = true := by decide
'''
    def observed(state,value):
        return state['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    tp={**template['points'],'input':template['windows'][template_offset][0],
        'first':template['windows'][template_offset][1],'second':template['windows'][template_offset][2],
        'selected':template['windows'][template_offset][3],'result':template['windows'][template_offset][4]}
    ap={**target['points'],'input':target['windows'][target_offset][0],
        'first':target['windows'][target_offset][1],'second':target['windows'][target_offset][2],
        'selected':target['windows'][target_offset][3],'result':target['windows'][target_offset][4]}
    roles=('base','twice','triple','input','first','second','selected','result')
    for role in roles:
        a,b=(observed(target,v) for v in ap[role])
        source+=f'def {role} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(a)}, eval rho {linear(b)}⟩\n'
        source+=f'''theorem {role}_renamed {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    {T}.{role} (fun column => rho (columns column)) = {role} rho := by
  apply congrArg₂ Group.Point.mk
'''
        for tv,av in zip(tp[role],ap[role]):
            tl,al=observed(template,tv),observed(target,av)
            source+=f'''  · change eval (fun column => rho (columns column)) {linear(tl)} = eval rho {linear(al)}
    exact RowRenaming.checked_linear rho columns {linear(tl)} {linear(al)} (by decide)
'''
    ti=2*(125-template['metadata']['window_start']-template_offset)
    ai=2*(125-target['metadata']['window_start']-target_offset)
    for role,th,ah in zip(('low','high'),template['bits'][ti:ti+2],target['bits'][ai:ai+2]):
        tl,al=template['derived'][th],target['derived'][ah]
        source+=f'''def {role} : Linear := {linear(al)}
theorem {role}_renamed {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    eval (fun column => rho (columns column)) {T}.{role} = eval rho {role} := by
  exact RowRenaming.checked_linear rho columns {linear(tl)} {linear(al)} (by decide)
'''
    source+=f'''theorem arithmetic_window {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.DoubleEquations (input rho) (first rho) ∧
    TransferOwnership.DoubleEquations (first rho) (second rho) ∧
    TransferOwnership.AddEquations (coefficientD : F) (second rho) (selected rho) (result rho) ∧
    selected rho = Group.windowPoint (eval rho low) (eval rho high)
      (base rho) (twice rho) (triple rho) := by
  have templateRows := RowRenaming.checked_rows rho columns {T}.rawRows rawRows rows_checked satisfied
  have templateOne : (fun column => rho (columns column)) 0 = 1 := by
    simpa only [columns_zero] using one
  have result := {T}.arithmetic_window (fun column => rho (columns column)) templateOne four templateRows
  rw [input_renamed, first_renamed, second_renamed, selected_renamed, result_renamed,
      low_renamed, high_renamed, base_renamed, twice_renamed, triple_renamed] at result
  exact result
'''
    for name in ('columns_zero','rows_checked')+tuple(role+'_renamed' for role in roles)+('low_renamed','high_renamed','arithmetic_window'):
        source+='#print axioms '+name+'\n'
    source+='end ShielddSecurity.'+namespace+'\n'
    return _signature_audits(source)


def generate_window_instances(chunks, extractions):
    """Bounded source candidates for a complete observed ownership loop.

    This yields source only. Each named module still needs its independent
    kernel check, and the resulting common-assignment trace must be composed.
    """
    join_chunks(chunks)
    if not isinstance(extractions,list) or len(extractions)!=len(chunks):
        raise relation.RelationError('ownership instance extraction count')
    template_index=next((i for i,c in enumerate(chunks)
                         if c['metadata']['window_start']<=16<
                         c['metadata']['window_start']+c['metadata']['window_count']),None)
    if template_index is None:raise relation.RelationError('missing ownership template window')
    template=chunks[template_index];template_rows=extractions[template_index]
    template_offset=16-template['metadata']['window_start']
    for chunk,rows in zip(chunks,extractions):
        metadata_hash=chunk.get('metadata_sha256')
        if not isinstance(metadata_hash,str) or not re.fullmatch('[0-9a-f]{64}',metadata_hash):
            raise relation.RelationError('ownership instances require strict-ingress raw metadata identity')
        for offset in range(chunk['metadata']['window_count']):
            index=chunk['metadata']['window_start']+offset
            namespace=f'RuntimeOwnershipWindow{index:03d}'
            if index in (0,16):
                source=generate_window_equations(chunk,rows,metadata_hash,offset,namespace,
                                                include_precompute=(index==0))
            else:
                source=generate_renamed_window(template,template_rows,chunk,rows,
                    template_offset,offset,namespace=namespace)
            yield namespace,source,{'window':index,'template':None if index==0 else 16,
                'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
                'scope':'generated actual-row candidate; kernel/trace/source/group qualification pending'}


def generate_trace_chunk(checked, extracted):
    """Compose at most sixteen checked windows with their actual Boolean rows.

    The generated conclusion is an arithmetic trace under one assignment.
    Sender representation, final endpoint and scalar reconstruction are later
    joins; this generator does not add those conclusions as premises.
    """
    from .generate_hash_round import linear, _signature_audits
    start = checked['metadata']['window_start']
    count = checked['metadata']['window_count']
    if type(start) is not int or type(count) is not int or not 1 <= count <= 16:
        raise relation.RelationError('bounded ownership trace chunk required')
    if not 0 <= start < start + count <= 126:
        raise relation.RelationError('ownership trace window interval')
    identity = extracted.get('identity', {})
    if (identity.get('relation_digest') != checked['metadata']['relation_digest'] or
            identity.get('stored_rows') != checked['metadata']['full_rows'] or
            identity.get('domain_size') != checked['metadata']['domain_size']):
        raise relation.RelationError('ownership trace extraction identity/shape mismatch')
    modules = [f'RuntimeOwnershipWindow{i:03d}' for i in range(start, start + count)]
    qualified = ['ShielddSecurity.' + m for m in modules]
    namespace = f'RuntimeOwnershipTrace{start:03d}'
    roles = {role: entry['row'] for entry in extracted['templates'] for role in entry['roles']}
    rowmap = {row['row']: row for row in extracted['selected_rows']}
    indices, bit_rows = [], []
    for index in range(start, start + count):
        for bit_index in (2 * (125 - index), 2 * (125 - index) + 1):
            row_index = roles.get(f'bit.{bit_index}')
            if row_index not in rowmap:
                raise relation.RelationError('ownership trace missing actual Boolean row')
            row = rowmap[row_index]
            a = tuple((c, int(v, 16)) for c, v in row['a'])
            b = tuple((c, int(v, 16)) for c, v in row['b'])
            if a != checked['derived'][checked['bits'][bit_index]] or b != a:
                raise relation.RelationError('ownership trace wrong Boolean role')
            indices.append(row_index)
            bit_rows.append((a, b))
    source = ''.join(f'import ShielddSecurity.{m}\n' for m in modules)
    source += f'''import ShielddSecurity.ScalarBits
set_option maxHeartbeats 500000
namespace ShielddSecurity.{namespace}
def modulus : Nat := {relation.MODULUS}
def coefficientD : Int := {qualified[0]}.coefficientD
def originalBitRows : List Nat := {indices}
def bitRows : List Row := [
'''
    source += ',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩' for a, b in bit_rows) + ']\n'
    source += 'def bits : List Linear := [' + ', '.join(q + '.' + bit for q in qualified for bit in ('low', 'high')) + ']\n'
    source += 'def windowRows : List (List Row) := [' + ', '.join(q + '.rawRows' for q in qualified) + ']\n'
    source += 'def rawRows : List Row := windowRows.flatten ++ bitRows\n'
    source += 'theorem checked_bits : ScalarBits.checkBits modulus bitRows bits = true := by decide\n'
    source += f'''def base {{F : Type}} [Field F] (rho : Nat → F) := {qualified[0]}.base rho
def twice {{F : Type}} [Field F] (rho : Nat → F) := {qualified[0]}.twice rho
def triple {{F : Type}} [Field F] (rho : Nat → F) := {qualified[0]}.triple rho
def input {{F : Type}} [Field F] (rho : Nat → F) := {qualified[0]}.input rho
'''
    for offset, q in enumerate(qualified):
        source += f'''noncomputable def window{offset} {{F : Type}} [Field F] (rho : Nat → F) : TransferOwnership.WindowWitness F :=
  ⟨ScalarBits.decodeBit rho {q}.low, ScalarBits.decodeBit rho {q}.high,
    {q}.first rho, {q}.second rho, {q}.result rho⟩
'''
    source += 'noncomputable def windows {F : Type} [Field F] (rho : Nat → F) := [' + ', '.join(f'window{i} rho' for i in range(count)) + ']\n'
    for offset, q in enumerate(qualified):
        member = 'List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(offset):
            member = 'List.mem_cons.mpr (Or.inr (' + member + '))'
        source += f'''theorem window{offset}_equations {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.WindowEquations (coefficientD : F) (base rho) (twice rho) (triple rho)
      ({q}.input rho) (window{offset} rho) := by
  have arith : Satisfies rho {q}.rawRows := by
    intro row member
    apply satisfied row
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_flatten.mpr
    refine ⟨{q}.rawRows, ?_, member⟩
    exact {member}
  have bitSat : Satisfies rho bitRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  have lowValue := ScalarBits.checked_bit_value rho bitRows bitSat bits checked_bits
    {q}.low (by exact '''
        low_member = 'List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(2 * offset):
            low_member = 'List.mem_cons.mpr (Or.inr (' + low_member + '))'
        high_member = 'List.mem_cons.mpr (Or.inr (' + low_member + '))'
        source += low_member + ')\n'
        source += f'''  have highValue := ScalarBits.checked_bit_value rho bitRows bitSat bits checked_bits
    {q}.high (by exact {high_member})
'''
        facts = '⟨_, _, firstRows, secondRows, addRows, selected⟩' if start + offset == 0 else '⟨firstRows, secondRows, addRows, selected⟩'
        source += f'''  rcases {q}.arithmetic_window rho one four arith with {facts}
  rw [selected, lowValue, highValue] at addRows
  exact ⟨firstRows, secondRows, addRows⟩
'''
    source += f'''theorem actual_trace_equations {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.TraceEquations (coefficientD : F) (base rho) (twice rho) (triple rho)
      (input rho) (windows rho) := by
  simp only [windows, TransferOwnership.TraceEquations]
  exact '''
    chain = 'True.intro'
    for offset in reversed(range(count)):
        chain = f'⟨window{offset}_equations rho one four satisfied, {chain}⟩'
    source += chain + '\n'
    source += f'''theorem output_role {{F : Type}} [Field F] (rho : Nat → F) :
    TransferOwnership.traceOutput (input rho) (windows rho) = {qualified[-1]}.result rho := by rfl
'''
    for name in ['checked_bits'] + [f'window{i}_equations' for i in range(count)] + ['actual_trace_equations', 'output_role']:
        source += '#print axioms ' + name + '\n'
    source += 'end ShielddSecurity.' + namespace + '\n'
    return _signature_audits(source)


def generate_trace_composition(chunks, extractions):
    """Compose the eight actual arithmetic traces; sender representation stays explicit."""
    from .generate_hash_round import linear, _signature_audits
    join_chunks(chunks)
    if len(chunks) != 8 or len(extractions) != 8:
        raise relation.RelationError('ownership trace composition requires eight chunks')
    names = [f"ShielddSecurity.RuntimeOwnershipTrace{c['metadata']['window_start']:03d}" for c in chunks]
    columns, original_bits = [], []
    raw = {}
    for chunk, extracted in zip(chunks, extractions):
        # Reuse the strict bit/identity validation of the bounded emitter.
        generate_trace_chunk(chunk, extracted)
        for row in extracted['selected_rows']:
            if row['row'] in raw and row != raw[row['row']]:
                raise relation.RelationError('ownership composition overlapping rows')
            raw[row['row']] = row
    role_rows = {role: entry['row'] for extracted in extractions
                 for entry in extracted['templates'] for role in entry['roles']}
    for index, handle in enumerate(chunks[0]['bits']):
        lc = chunks[0]['derived'][handle]
        if len(lc) != 1 or lc[0][1] != 1:
            raise relation.RelationError('ownership scalar bit must be an exact unit column')
        row_index = role_rows.get(f'bit.{index}')
        if row_index not in raw:
            raise relation.RelationError('ownership composition missing global Boolean row')
        expected = [[lc[0][0], f'{1:064x}']]
        if raw[row_index]['a'] != expected or raw[row_index]['b'] != expected:
            raise relation.RelationError('ownership composition global Boolean mismatch')
        columns.append(lc[0][0]); original_bits.append(row_index)
    endpoints = [role_rows.get('target.' + str(axis)) for axis in range(2)]
    if any(index not in raw for index in endpoints):
        raise relation.RelationError('ownership composition missing endpoint')
    endpoint_rows = [tuple(tuple((c, int(v, 16)) for c, v in raw[index][key])
                           for key in ('a', 'b')) for index in endpoints]
    def observed(value):
        return chunks[-1]['derived'][value[1]] if value[0] == 'source' else canonical([(0, value[1])])
    output = [observed(value) for value in chunks[-1]['points']['output']]
    target = [observed(value) for value in chunks[-1]['points']['target']]
    for row, left, right in zip(endpoint_rows, output, target):
        if row != (combine(left, right, -1), ()):
            raise relation.RelationError('ownership composition endpoint orientation')
    source = ''.join('import ' + name + '\n' for name in names)
    source += '''import ShielddSecurity.RuntimeTransferCurveParameters
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeTransferOwnership
'''
    source += f'''def modulus : Nat := {relation.MODULUS}
def coefficientD : Int := {names[0]}.coefficientD
def originalBitRows : List Nat := {original_bits}
def columns : List Nat := {columns}
def bits : List Linear := columns.map (fun column => [(column, 1)])
def bitRows : List Row := columns.map booleanRow
def originalEndpointRows : List Nat := {endpoints}
def endpointRows : List Row := [
'''
    source += ',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩' for a, b in endpoint_rows) + ']\n'
    source += 'def chunkRows : List (List Row) := [' + ', '.join(name + '.rawRows' for name in names) + ']\n'
    source += 'def rawRows : List Row := chunkRows.flatten ++ (bitRows ++ endpointRows)\n'
    for role in ('base', 'twice', 'triple', 'input'):
        source += f'def {role} {{F : Type}} [Field F] (rho : Nat → F) := {names[0]}.{role} rho\n'
    source += f'def target {{F : Type}} [Field F] (rho : Nat → F) := Group.Point.mk (eval rho {linear(target[0])}) (eval rho {linear(target[1])})\n'
    # Explicit right association agrees with the append lemmas and avoids a
    # wide constraint walk. Each imported bounded module supplies its own trace.
    windows = names[-1] + '.windows rho'
    for name in reversed(names[:-1]): windows = name + '.windows rho ++ (' + windows + ')'
    source += f'noncomputable def windows {{F : Type}} [Field F] (rho : Nat → F) := {windows}\n'
    for offset, name in enumerate(names):
        member = 'List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(offset): member = 'List.mem_cons.mpr (Or.inr (' + member + '))'
        source += f'''theorem chunk{offset}_satisfied {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho rawRows) : Satisfies rho {name}.rawRows := by
  intro row member
  apply satisfied row
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_flatten.mpr
  refine ⟨{name}.rawRows, ?_, member⟩
  exact {member}
'''
    source += '''theorem actual_trace {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.TraceEquations (coefficientD : F) (base rho) (twice rho) (triple rho)
      (input rho) (windows rho) := by
'''
    for offset, name in enumerate(names):
        source += f'  have eq{offset} := {name}.actual_trace_equations rho one four (chunk{offset}_satisfied rho satisfied)\n'
    source += f'  have tail7 := eq7\n'
    suffix = names[-1] + '.windows rho'
    for offset in reversed(range(7)):
        name = names[offset]
        suffix = name + '.windows rho ++ (' + suffix + ')'
        source += f'''  have tail{offset} : TransferOwnership.TraceEquations (coefficientD : F)
      (base rho) (twice rho) (triple rho) ({name}.input rho) ({suffix}) := by
    apply (TransferOwnership.trace_equations_append _ _ _ _ _ _ _).mpr
    refine ⟨eq{offset}, ?_⟩
    simpa only [{name}.output_role] using tail{offset + 1}
'''
    source += '  exact tail0\n'
    source += '''private theorem bool_nat (b : Bool) : b.toNat = (if b then 1 else 0) := by
  cases b <;> rfl
theorem digits_order {F : Type} [Field F] (rho : Nat → F) :
    (windows rho).map (fun window => window.low.toNat + 2 * window.high.toNat) =
      (TransferWindows.pairDigits (ScalarBits.decodeBits rho bits)).reverse := by
'''
    digit_bools = [f'ScalarBits.decodeBit rho [({column}, 1)]' for column in columns]
    left_digits, right_digits = [], []
    for i in reversed(range(126)):
        lo, hi = digit_bools[2 * i:2 * i + 2]
        left_digits.append(f'({lo}).toNat + 2 * ({hi}).toNat')
        right_digits.append(f'(if {lo} then 1 else 0) + 2 * (if {hi} then 1 else 0)')
    source += '  change [' + ', '.join(left_digits) + '] = [' + ', '.join(right_digits) + ']\n'
    source += '  simp only [bool_nat]\n'
    source += f'''theorem output_role {{F : Type}} [Field F] (rho : Nat → F) :
    TransferOwnership.traceOutput (input rho) (windows rho) =
      ShielddSecurity.RuntimeOwnershipWindow125.result rho := by
'''
    source += '  unfold windows input\n'
    for offset, name in enumerate(names[:-1]):
        suffix = names[-1] + '.windows rho'
        for following in reversed(names[offset:-1]):
            suffix = following + '.windows rho ++ (' + suffix + ')'
        source += f'  change TransferOwnership.traceOutput ({name}.input rho) ({suffix}) = ShielddSecurity.RuntimeOwnershipWindow125.result rho\n'
        source += f'  rw [TransferOwnership.trace_output_append, {name}.output_role]\n'
    source += f'  change TransferOwnership.traceOutput ({names[-1]}.input rho) ({names[-1]}.windows rho) = ShielddSecurity.RuntimeOwnershipWindow125.result rho\n'
    source += f'  exact {names[-1]}.output_role rho\n'
    for axis in range(2):
        source += f'''theorem endpoint{axis}_checked : Compiler.checkRow modulus endpointRows
    ⟨Compiler.subtract {linear(output[axis])} {linear(target[axis])}, []⟩ = true := by decide
'''
    source += '''theorem target_role {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ShielddSecurity.RuntimeOwnershipWindow125.result rho = target rho := by
  have endpointSat : Satisfies rho endpointRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
'''
    for axis in range(2):
        source += f'  have axis{axis} := Compiler.checked_assertion_sound rho endpointRows {linear(output[axis])} {linear(target[axis])} endpointSat endpoint{axis}_checked\n'
    source += '''  exact congrArg₂ Group.Point.mk axis0 axis1
theorem actual_ownership {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (coefficientD : F)) (senderBase : J)
    (baseRole : base rho = model.coordinates senderBase)
    (satisfied : Satisfies rho rawRows) :
    target rho = model.coordinates (ShielddSecurity.binary (ScalarBits.decodeBits rho bits) • senderBase) := by
  have firstSat := chunk0_satisfied rho satisfied
  have initial : Satisfies rho ShielddSecurity.RuntimeOwnershipWindow000.rawRows := by
    intro row member
    apply firstSat row
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_flatten.mpr
    refine ⟨ShielddSecurity.RuntimeOwnershipWindow000.rawRows, ?_, member⟩
    exact List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨doubleRows, addRows, _, _, _, _⟩ :=
    ShielddSecurity.RuntimeOwnershipWindow000.arithmetic_window rho one four initial
  change TransferOwnership.DoubleEquations (base rho) (twice rho) at doubleRows
  change TransferOwnership.AddEquations (coefficientD : F) (twice rho) (base rho) (triple rho) at addRows
  rw [baseRole] at doubleRows addRows
  have parameters := RuntimeTransferCurveParameters.actual_curve_parameters codec
  have inputRole : input rho = model.coordinates 0 := by
    rw [model.identity]
    simp [input, ShielddSecurity.RuntimeOwnershipTrace000.input,
      ShielddSecurity.RuntimeOwnershipWindow000.input, eval, one, Group.identityPoint]
  have trace := actual_trace rho one four satisfied
  rw [baseRole, inputRole] at trace
  have result := TransferOwnership.trace_scalar_coordinates (coefficientD : F)
    (RuntimeJubjub.imaginary : F) model parameters.1 parameters.2.1 senderBase
    (twice rho) (triple rho) doubleRows addRows (windows rho)
    (ScalarBits.decodeBits rho bits) (digits_order rho) trace
  rw [← inputRole, output_role rho, target_role rho satisfied] at result
  exact result
'''
    for name in [f'chunk{i}_satisfied' for i in range(8)] + ['actual_trace', 'digits_order',
            'output_role', 'endpoint0_checked', 'endpoint1_checked', 'target_role', 'actual_ownership']:
        source += '#print axioms ' + name + '\n'
    source += 'end ShielddSecurity.RuntimeTransferOwnership\n'
    return _signature_audits(source)


def rnk_column_candidate(column):
    """Search candidate only; every transported row requires exact acceptance."""
    if 1504 <= column <= 1505:
        return column + 16
    if 2253 <= column <= 3008:
        return column + 756
    if 51214 <= column <= 55994:
        return column + 4781
    return column


def extract_rnk_row_transport(chunks, extractions, stream, expected_relation):
    """Match all loop arithmetic rows without inventing source observations.

    Owner endpoint assertions are excluded. The fixed candidate substitutions
    have no authority until their complete rows match the ordinary relation.
    """
    join_chunks(chunks)
    if len(chunks) != 8 or len(extractions) != 8:
        raise relation.RelationError('RNK row transport requires eight owner chunks')
    if any(chunk['metadata']['schema'] != 'shieldd-transfer-ownership-v1' for chunk in chunks):
        raise relation.RelationError('RNK row transport requires owner observations')
    if [(c['metadata']['window_start'], c['metadata']['window_count']) for c in chunks] != [
            (i,min(16,126-i)) for i in range(0,126,16)]:
        raise relation.RelationError('RNK row transport canonical layout required')
    if chunks[0]['metadata']['relation_digest'] != expected_relation:
        raise relation.RelationError('RNK row transport relation mismatch')
    specifications = []
    expected = {}
    for chunk, extraction in zip(chunks, extractions):
        blocks = []
        for offset in range(chunk['metadata']['window_count']):
            initial = chunk['metadata']['window_start'] + offset == 0
            cones = cone_certificates(chunk, extraction, offset, initial)
            quotients = quotient_certificates(chunk, extraction, offset, initial)
            rows = dict(cones['rows'])
            for index, row in quotients['rows'].items():
                if index in rows and rows[index] != row:
                    raise relation.RelationError('RNK source row disagreement')
                rows[index] = row
            blocks.append(rows)
        roles = {role: entry['row'] for entry in extraction['templates'] for role in entry['roles']}
        bit_rows = {}
        rowmap = {row['row']: row for row in extraction['selected_rows']}
        start = chunk['metadata']['window_start']
        count = chunk['metadata']['window_count']
        for index in range(2*(126-start-count), 2*(126-start)):
            handle = chunk['bits'][index]
            lc = chunk['derived'][handle]
            if any(rnk_column_candidate(column) != column for column, _ in lc):
                raise relation.RelationError('RNK transport changes scalar bit')
            row = rowmap[roles[f'bit.{index}']]
            bit_rows[row['row']] = tuple(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        blocks.append(bit_rows)
        for block in blocks:
            for row in block.values():
                mapped = tuple(canonical((rnk_column_candidate(c),v) for c,v in lc) for lc in row)
                expected.setdefault(mapped, None)
        specifications.append({'start': start, 'count': count, 'source_blocks': blocks})
    def visit(row):
        index = row['row']
        key = tuple(tuple((c,int(v,16)) for c,v in row[name]) for name in ('a','b'))
        if key in expected and expected[key] is None:
            expected[key] = (index, row)
    identity = relation.inspect(stream, expected_relation=expected_relation, row_observer=visit)
    if (identity['domain_size'] != chunks[0]['metadata']['domain_size'] or
            identity['stored_rows'] != chunks[0]['metadata']['full_rows']):
        raise relation.RelationError('RNK row transport ordinary shape mismatch')
    if any(value is None for value in expected.values()):
        raise relation.RelationError('missing actual RNK transported arithmetic row')
    for specification in specifications:
        target_blocks = []
        for block in specification.pop('source_blocks'):
            target = {}
            for row in block.values():
                mapped = tuple(canonical((rnk_column_candidate(c),v) for c,v in lc) for lc in row)
                index, actual = expected[mapped]
                target[index] = actual
            target_blocks.append([target[index] for index in sorted(target)])
        specification['blocks'] = target_blocks
    return {'identity': identity, 'chunks': specifications,
            'scope': 'actual RNK arithmetic row transport; owner endpoint assertions excluded; source boundary joins separate'}


def generate_rnk_row_trace(specification, identity):
    """Emit a bounded actual-row transport, with no synthetic observer record."""
    from .generate_hash_round import linear, _signature_audits
    start, count = specification['start'], specification['count']
    if (start, count) not in [(i,min(16,126-i)) for i in range(0,126,16)]:
        raise relation.RelationError('RNK row trace canonical interval required')
    blocks = specification['blocks']
    if len(blocks) != count + 1:
        raise relation.RelationError('RNK row trace block count')
    owner = f'ShielddSecurity.RuntimeOwnershipTrace{start:03d}'
    namespace = f'ShielddSecurity.RuntimeRnkTrace{start:03d}'
    source = f'''-- Actual ordinary relation: {identity['relation_digest']}
-- Row-only transport; no RNK observer metadata is synthesized.
import {owner}
import ShielddSecurity.RowRenaming
set_option maxHeartbeats 500000
namespace {namespace}
def modulus : Nat := {relation.MODULUS}
def coefficientD : Int := {owner}.coefficientD
def columns (column : Nat) : Nat :=
  if 1504 ≤ column ∧ column ≤ 1505 then column + 16
  else if 2253 ≤ column ∧ column ≤ 3008 then column + 756
  else if 51214 ≤ column ∧ column ≤ 55994 then column + 4781
  else column
theorem columns_zero : columns 0 = 0 := by decide
'''
    for offset, rows in enumerate(blocks):
        source += f'def originalRows{offset} : List Nat := {[row["row"] for row in rows]}\n'
        source += f'def rows{offset} : List Row := [\n'
        entries = []
        for row in rows:
            for key in ('a','b'):
                relation.terms(row[key],identity['domain_size'])
            a,b = [tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b')]
            entries.append('  ⟨'+linear(a)+', '+linear(b)+'⟩')
        source += ',\n'.join(entries)+']\n'
    source += 'def blocks : List (List Row) := ['+', '.join(f'rows{i}' for i in range(count+1))+']\n'
    source += 'def rawRows : List Row := blocks.flatten\n'
    for role in ('base','twice','triple','input'):
        source += f'def {role} {{F : Type}} [Field F] (rho : Nat → F) := {owner}.{role} (fun column => rho (columns column))\n'
    for offset in range(count):
        module = f'ShielddSecurity.RuntimeOwnershipWindow{start+offset:03d}'
        source += f'def window{offset}_output {{F : Type}} [Field F] (rho : Nat → F) := {module}.result (fun column => rho (columns column))\n'
    source += f'noncomputable def windows {{F : Type}} [Field F] (rho : Nat → F) := {owner}.windows (fun column => rho (columns column))\n'
    sources = [f'ShielddSecurity.RuntimeOwnershipWindow{i:03d}.rawRows' for i in range(start,start+count)] + [owner+'.bitRows']
    for offset, old_rows in enumerate(sources):
        source += f'''private theorem block{offset}_satisfied {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => rho (columns column)) {old_rows} := by
  apply RowRenaming.checked_rows rho columns {old_rows} rows{offset} (by decide)
  intro row member
  apply satisfied row
  apply List.mem_flatten.mpr
  refine ⟨rows{offset}, ?_, member⟩
'''
        member='List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(offset): member='List.mem_cons.mpr (Or.inr ('+member+'))'
        source += '  exact '+member+'\n'
    source += f'''theorem source_satisfied {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => rho (columns column)) {owner}.rawRows := by
  intro row member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_flatten.mp member with ⟨block, present, member⟩
    simp only [{owner}.windowRows, List.mem_cons, List.not_mem_nil, or_false] at present
'''
    branches = ' | '.join(f'h{i}' for i in range(count))
    source += f'    rcases present with {branches}\n'
    for offset in range(count):
        source += f'    · subst block; exact block{offset}_satisfied rho satisfied row member\n'
    source += f'  · exact block{count}_satisfied rho satisfied row member\n'
    source += f'''theorem actual_trace_equations {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.TraceEquations (coefficientD : F) (base rho) (twice rho) (triple rho)
      (input rho) (windows rho) := by
  have zero : rho (columns 0) = 1 := by rw [columns_zero]; exact one
  exact {owner}.actual_trace_equations (fun column => rho (columns column)) zero four
    (source_satisfied rho satisfied)
#print axioms columns_zero
#print axioms source_satisfied
#print axioms actual_trace_equations
end {namespace}
'''
    return _signature_audits(source)


def _validate_rnk_composition_extraction(chunk, extracted):
    if chunk['metadata']['schema'] != 'shieldd-transfer-rnk-dh-v1':
        raise relation.RelationError('RNK composition requires RNK observations')
    identity = extracted['identity']
    if (identity['relation_digest'] != chunk['metadata']['relation_digest'] or
            identity['domain_size'] != chunk['metadata']['domain_size'] or
            identity['stored_rows'] != chunk['metadata']['full_rows']):
        raise relation.RelationError('RNK composition extraction identity mismatch')
    # The same bounded selector validates actual bit/source roles and row shapes.
    cone_certificates(chunk, extracted, window_offset=0, include_precompute=True)


def generate_rnk_trace_composition(chunks, extractions, *, row_transport=None, rnk_boundary=None):
    """Compose actual RNK arithmetic traces without owner endpoint assertions."""
    from .generate_hash_round import linear, _signature_audits
    join_chunks(chunks)
    if len(chunks) != 8 or len(extractions) != 8:
        raise relation.RelationError('ownership trace composition requires eight chunks')
    layout = [(chunk['metadata']['window_start'], chunk['metadata']['window_count']) for chunk in chunks]
    if layout != [(start, min(16, 126-start)) for start in range(0,126,16)]:
        raise relation.RelationError('RNK composition requires canonical eight-chunk layout')
    if row_transport is not None:
        if rnk_boundary is None or rnk_boundary['metadata']['schema'] != 'shieldd-transfer-rnk-dh-v1':
            raise relation.RelationError('RNK row composition requires actual RNK boundary')
        if any(c['metadata']['schema'] != 'shieldd-transfer-ownership-v1' for c in chunks):
            raise relation.RelationError('RNK row composition requires owner templates')
        identity = row_transport['identity']
        if any((c['metadata']['relation_digest'] != identity['relation_digest'] or
                c['metadata']['domain_size'] != identity['domain_size'] or
                c['metadata']['full_rows'] != identity['stored_rows']) for c in chunks):
            raise relation.RelationError('RNK row composition owner identity mismatch')
        if (identity['relation_digest'] != rnk_boundary['metadata']['relation_digest'] or
                identity['domain_size'] != rnk_boundary['metadata']['domain_size'] or
                identity['stored_rows'] != rnk_boundary['metadata']['full_rows']):
            raise relation.RelationError('RNK row composition boundary identity mismatch')
        if [(c['start'],c['count']) for c in row_transport['chunks']] != layout:
            raise relation.RelationError('RNK row composition transport layout mismatch')
        if chunks[0]['bits'] != rnk_boundary['bits']:
            raise relation.RelationError('RNK row composition scalar bit source mismatch')
        def point_lc(chunk, value):
            return chunk['derived'][value[1]] if value[0] == 'source' else canonical([(0,value[1])])
        for role, owner_chunk in [('base',chunks[0]),('output',chunks[-1])]:
            mapped = [canonical((rnk_column_candidate(c),v) for c,v in point_lc(owner_chunk,value))
                      for value in owner_chunk['points'][role]]
            observed = [point_lc(rnk_boundary,value) for value in rnk_boundary['points'][role]]
            if mapped != observed:
                raise relation.RelationError('RNK row composition captured point boundary mismatch')
    names = [f"ShielddSecurity.RuntimeRnkTrace{c['metadata']['window_start']:03d}" for c in chunks]
    columns, original_bits = [], []
    raw = {}
    for chunk, extracted in zip(chunks, extractions):
        # Reuse the strict bit/identity validation of the bounded emitter.
        if row_transport is None:
            _validate_rnk_composition_extraction(chunk, extracted)
        else:
            cone_certificates(chunk,extracted,window_offset=0,include_precompute=True)
        for row in extracted['selected_rows']:
            if row['row'] in raw and row != raw[row['row']]:
                raise relation.RelationError('ownership composition overlapping rows')
            raw[row['row']] = row
    role_rows = {role: entry['row'] for extracted in extractions
                 for entry in extracted['templates'] for role in entry['roles']}
    for index, handle in enumerate(chunks[0]['bits']):
        lc = chunks[0]['derived'][handle]
        if len(lc) != 1 or lc[0][1] != 1:
            raise relation.RelationError('ownership scalar bit must be an exact unit column')
        row_index = role_rows.get(f'bit.{index}')
        if row_index not in raw:
            raise relation.RelationError('ownership composition missing global Boolean row')
        expected = [[lc[0][0], f'{1:064x}']]
        if raw[row_index]['a'] != expected or raw[row_index]['b'] != expected:
            raise relation.RelationError('ownership composition global Boolean mismatch')
        columns.append(lc[0][0]); original_bits.append(row_index)
    source = ''.join('import ' + name + '\n' for name in names)
    source += '''import ShielddSecurity.RuntimeTransferCurveParameters
import ShielddSecurity.RuntimeRnkPrecompute
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeTransferRnkLoop
'''
    source += f'''def modulus : Nat := {relation.MODULUS}
def coefficientD : Int := {names[0]}.coefficientD
def originalBitRows : List Nat := {original_bits}
def columns : List Nat := {columns}
def bits : List Linear := columns.map (fun column => [(column, 1)])
def bitRows : List Row := columns.map booleanRow
'''
    source += 'def chunkRows : List (List Row) := [' + ', '.join(name + '.rawRows' for name in names) + ']\n'
    source += 'def rawRows : List Row := chunkRows.flatten ++ bitRows\n'
    for role in ('base', 'twice', 'triple', 'input'):
        source += f'def {role} {{F : Type}} [Field F] (rho : Nat → F) := {names[0]}.{role} rho\n'
    # Explicit right association agrees with the append lemmas and avoids a
    # wide constraint walk. Each imported bounded module supplies its own trace.
    windows = names[-1] + '.windows rho'
    for name in reversed(names[:-1]): windows = name + '.windows rho ++ (' + windows + ')'
    source += f'noncomputable def windows {{F : Type}} [Field F] (rho : Nat → F) := {windows}\n'
    for offset, name in enumerate(names):
        member = 'List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(offset): member = 'List.mem_cons.mpr (Or.inr (' + member + '))'
        source += f'''theorem chunk{offset}_satisfied {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho rawRows) : Satisfies rho {name}.rawRows := by
  intro row member
  apply satisfied row
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_flatten.mpr
  refine ⟨{name}.rawRows, ?_, member⟩
  exact {member}
'''
    for offset, name in enumerate(names):
        count = chunks[offset]['metadata']['window_count']
        source += f"""theorem chunk{offset}_output {{F : Type}} [Field F] (rho : Nat → F) :
    TransferOwnership.traceOutput ({name}.input rho) ({name}.windows rho) =
      {name}.window{count-1}_output rho := by rfl
"""
    source += '''theorem actual_trace {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.TraceEquations (coefficientD : F) (base rho) (twice rho) (triple rho)
      (input rho) (windows rho) := by
'''
    for offset, name in enumerate(names):
        source += f'  have eq{offset} := {name}.actual_trace_equations rho one four (chunk{offset}_satisfied rho satisfied)\n'
    source += f'  have tail7 := eq7\n'
    suffix = names[-1] + '.windows rho'
    for offset in reversed(range(7)):
        name = names[offset]
        suffix = name + '.windows rho ++ (' + suffix + ')'
        source += f'''  have tail{offset} : TransferOwnership.TraceEquations (coefficientD : F)
      (base rho) (twice rho) (triple rho) ({name}.input rho) ({suffix}) := by
    apply (TransferOwnership.trace_equations_append _ _ _ _ _ _ _).mpr
    refine ⟨eq{offset}, ?_⟩
    simpa only [chunk{offset}_output] using tail{offset + 1}
'''
    source += '  exact tail0\n'
    source += '''private theorem bool_nat (b : Bool) : b.toNat = (if b then 1 else 0) := by
  cases b <;> rfl
theorem digits_order {F : Type} [Field F] (rho : Nat → F) :
    (windows rho).map (fun window => window.low.toNat + 2 * window.high.toNat) =
      (TransferWindows.pairDigits (ScalarBits.decodeBits rho bits)).reverse := by
'''
    digit_bools = [f'ScalarBits.decodeBit rho [({column}, 1)]' for column in columns]
    left_digits, right_digits = [], []
    for i in reversed(range(126)):
        lo, hi = digit_bools[2 * i:2 * i + 2]
        left_digits.append(f'({lo}).toNat + 2 * ({hi}).toNat')
        right_digits.append(f'(if {lo} then 1 else 0) + 2 * (if {hi} then 1 else 0)')
    source += '  change [' + ', '.join(left_digits) + '] = [' + ', '.join(right_digits) + ']\n'
    source += '  simp only [bool_nat]\n'
    source += f'''theorem output_role {{F : Type}} [Field F] (rho : Nat → F) :
    TransferOwnership.traceOutput (input rho) (windows rho) =
      ShielddSecurity.RuntimeRnkTrace112.window13_output rho := by
'''
    source += '  unfold windows input\n'
    for offset, name in enumerate(names[:-1]):
        suffix = names[-1] + '.windows rho'
        for following in reversed(names[offset:-1]):
            suffix = following + '.windows rho ++ (' + suffix + ')'
        source += f'  change TransferOwnership.traceOutput ({name}.input rho) ({suffix}) = ShielddSecurity.RuntimeRnkTrace112.window13_output rho\n'
        source += f'  rw [TransferOwnership.trace_output_append, chunk{offset}_output]\n'
    source += f'  change TransferOwnership.traceOutput ({names[-1]}.input rho) ({names[-1]}.windows rho) = ShielddSecurity.RuntimeRnkTrace112.window13_output rho\n'
    source += '  exact chunk7_output rho\n'
    if row_transport is not None:
        boundary_output = [point_lc(rnk_boundary,value) for value in rnk_boundary['points']['output']]
        source += f'''theorem captured_output_role {{F : Type}} [Field F] (rho : Nat → F) :
    ShielddSecurity.RuntimeRnkTrace112.window13_output rho =
      Group.Point.mk (eval rho {linear(boundary_output[0])}) (eval rho {linear(boundary_output[1])}) := by rfl
'''
    source += '''theorem actual_multiplication {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (coefficientD : F)) (senderBase : J)
    (baseRole : base rho = model.coordinates senderBase)
    (satisfied : Satisfies rho rawRows) :
    ShielddSecurity.RuntimeRnkTrace112.window13_output rho = model.coordinates (ShielddSecurity.binary (ScalarBits.decodeBits rho bits) • senderBase) := by
  obtain ⟨doubleRows, addRows⟩ := RuntimeRnkPrecompute.actual_precompute rho one four
    (chunk0_satisfied rho satisfied)
  change TransferOwnership.DoubleEquations (base rho) (twice rho) at doubleRows
  change TransferOwnership.AddEquations (coefficientD : F) (twice rho) (base rho) (triple rho) at addRows
  rw [baseRole] at doubleRows addRows
  have parameters := RuntimeTransferCurveParameters.actual_curve_parameters codec
  have inputRole : input rho = model.coordinates 0 := by
    rw [model.identity]
    simp [input, ShielddSecurity.RuntimeRnkTrace000.input,
      eval, one, Group.identityPoint]
  have trace := actual_trace rho one four satisfied
  rw [baseRole, inputRole] at trace
  have result := TransferOwnership.trace_scalar_coordinates (coefficientD : F)
    (RuntimeJubjub.imaginary : F) model parameters.1 parameters.2.1 senderBase
    (twice rho) (triple rho) doubleRows addRows (windows rho)
    (ScalarBits.decodeBits rho bits) (digits_order rho) trace
  rw [← inputRole, output_role rho] at result
  exact result
'''
    if row_transport is not None:
        source += '#print axioms captured_output_role\n'
    for name in [f'chunk{i}_satisfied' for i in range(8)] + [f'chunk{i}_output' for i in range(8)] + ['actual_trace', 'digits_order',
            'output_role', 'actual_multiplication']:
        source += '#print axioms ' + name + '\n'
    source += 'end ShielddSecurity.RuntimeTransferRnkLoop\n'
    return _signature_audits(source)


def extract_cofactor_substitutions(template, requests, stream, expected_relation, *, cofactor_only=False):
    """Check complete renamed cofactor templates against the ordinary stream.

    Column shifts are candidate search inputs only. Every mapped physical row
    is required, and the emitted Lean checks use the fixed accepted AK theorem.
    Internal columns need no source-role names to transport its existential
    subgroup conclusion; the two claimed coordinates remain explicit roles.
    """
    if not isinstance(expected_relation, str) or not re.fullmatch('[0-9a-f]{64}', expected_relation):
        raise relation.RelationError('exact cofactor relation digest required')
    identity = template.get('identity', {})
    if identity.get('relation_digest') != expected_relation:
        raise relation.RelationError('cofactor template relation identity')
    domain = relation.natural(identity.get('domain_size'))
    count=71 if cofactor_only else 74
    if not isinstance(template.get('selected_rows'), list) or len(template['selected_rows']) != count:
        raise relation.RelationError(f'expected complete {count}-row cofactor template')
    if not isinstance(requests, list) or not 1 <= len(requests) <= 3:
        raise relation.RelationError('bounded cofactor substitution requests')
    source_rows = {}
    for row in template['selected_rows']:
        index = relation.natural(row['row'], identity['stored_rows'])
        if index in source_rows:
            raise relation.RelationError('duplicate cofactor template row')
        for terms in (row['a'], row['b']): relation.terms(terms, domain)
        source_rows[index] = tuple(tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
    source_columns = {c for row in source_rows.values() for lc in row for c, _ in lc}
    copy_rows = [(index, row) for index, row in source_rows.items()
                 if row[1] == () and len(row[0]) == 2 and row[0][0] == (0, 1)
                 and row[0][1][1] == relation.MODULUS - 1]
    if len(copy_rows) != 1:
        raise relation.RelationError('cofactor template constant-copy row')
    copy = copy_rows[0][1][0][1][0]
    expected, specifications = {}, []
    names = set()
    for request in requests:
        if not isinstance(request, dict) or set(request) != {'namespace', 'columns', 'point'}:
            raise relation.RelationError('cofactor substitution request schema')
        name, columns, point = request['namespace'], request['columns'], request['point']
        if not isinstance(name, str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*', name) or name in names:
            raise relation.RelationError('cofactor substitution namespace')
        names.add(name)
        if not isinstance(columns, dict) or set(columns) != source_columns:
            raise relation.RelationError('cofactor substitution must cover every source column')
        columns = {relation.natural(c, domain): relation.natural(v, domain) for c, v in columns.items()}
        if columns[0] != 0 or columns[copy] != copy:
            raise relation.RelationError('cofactor substitution constant roles')
        if not isinstance(point, (list, tuple)) or len(point) != 2:
            raise relation.RelationError('cofactor substitution point roles')
        point = tuple(canonical(lc) for lc in point)
        if point != (((columns[1980], 1),), ((columns[1981], 1),)):
            raise relation.RelationError('cofactor substitution claimed point mismatch')
        mapped = {index: tuple(canonical((columns[c], v) for c, v in lc) for lc in row)
                  for index, row in source_rows.items()}
        for value in mapped.values(): expected[value] = None
        specifications.append({'namespace': name, 'columns': sorted(columns.items()),
                               'point': point, 'mapped': mapped})
    observed = {}
    def visit(row):
        value = tuple(tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
        if value in expected and value not in observed: observed[value] = row
    actual_identity = relation.inspect(stream, expected_relation=expected_relation, row_observer=visit)
    if (actual_identity['domain_size'] != domain or
            actual_identity['stored_rows'] != identity['stored_rows']):
        raise relation.RelationError('cofactor substitution ordinary shape mismatch')
    if set(expected) != set(observed):
        raise relation.RelationError('missing actual renamed cofactor row')
    result = []
    for spec in specifications:
        pairs = [(index, observed[value]['row']) for index, value in sorted(spec['mapped'].items())]
        rows = {observed[value]['row']: observed[value] for value in spec['mapped'].values()}
        result.append({'namespace': spec['namespace'], 'columns': spec['columns'], 'point': spec['point'],
                       'row_pairs': pairs, 'selected_rows': [rows[i] for i in sorted(rows)],
                       'identity': actual_identity,
                       'scope': 'complete cofactor row substitution extraction; kernel/source-role integration pending'})
    return result


def generate_cofactor_substitution(extracted, *, cofactor_only=False):
    from .generate_hash_round import linear, _signature_audits
    name = extracted['namespace']
    if not isinstance(name, str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*', name):
        raise relation.RelationError('cofactor candidate namespace')
    source = f'''import ShielddSecurity.RuntimeTransferAk
import ShielddSecurity.RowRenaming
set_option maxHeartbeats 500000
namespace ShielddSecurity.{name}
def modulus : Nat := {relation.MODULUS}
def columnPairs : List (Nat × Nat) := {[(a, b) for a, b in extracted['columns']]}
def columns (column : Nat) : Nat :=
  ((columnPairs.find? (fun pair => pair.1 = column)).map Prod.snd).getD column
def originalRows : List Nat := {[row['row'] for row in extracted['selected_rows']]}
def rawRows : List Row := [
'''
    source += ',\n'.join('  ⟨' + linear(tuple((c, int(v, 16)) for c, v in row['a'])) + ', ' +
                         linear(tuple((c, int(v, 16)) for c, v in row['b'])) + '⟩'
                         for row in extracted['selected_rows']) + ']\n'
    source += f'''def point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(extracted['point'][0])}, eval rho {linear(extracted['point'][1])}⟩
theorem columns_zero : columns 0 = 0 := by decide
theorem rows_checked : ShielddSecurity.RuntimeTransferAk.rawRows.all
    (fun row => Compiler.checkRow modulus rawRows (RowRenaming.row columns row)) = true := by decide
theorem point_role {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    ShielddSecurity.RuntimeTransferAk.point (fun column => rho (columns column)) = point rho := by
  apply congrArg₂ Group.Point.mk
  · exact RowRenaming.checked_linear rho columns ShielddSecurity.RuntimeTransferAk.point_x
      {linear(extracted['point'][0])} (by decide)
  · exact RowRenaming.checked_linear rho columns ShielddSecurity.RuntimeTransferAk.point_y
      {linear(extracted['point'][1])} (by decide)
theorem actual_subgroup {{F J : Type}} [Field F] [CharP F modulus] [AddCommGroup J]
    (model : Group.StandardCurveModel J (ShielddSecurity.RuntimeTransferAkCones.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * ShielddSecurity.RuntimeTransferAk.subgroupOrder) • represented = 0)
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    ∃ represented : J, model.coordinates represented = point rho ∧
      ShielddSecurity.RuntimeTransferAk.subgroupOrder • represented = 0 ∧ represented ≠ 0 := by
  have source := RowRenaming.checked_rows rho columns ShielddSecurity.RuntimeTransferAk.rawRows rawRows rows_checked satisfied
  have zero : rho (columns 0) = 1 := by rw [columns_zero]; exact one
  obtain ⟨represented, coordinates, subgroup, nonidentity⟩ :=
    ShielddSecurity.RuntimeTransferAk.actual_ak_subgroup model standardOrder
      (fun column => rho (columns column)) zero source
  rw [point_role rho] at coordinates
  exact ⟨represented, coordinates, subgroup, nonidentity⟩
'''
    for theorem in ('columns_zero', 'rows_checked', 'point_role', 'actual_subgroup'):
        source += '#print axioms ' + theorem + '\n'
    source += 'end ShielddSecurity.' + name + '\n'
    if cofactor_only:
        source=source.replace('RuntimeTransferAkCones','RuntimeTransferCofactorCones').replace('RuntimeTransferAk','RuntimeTransferCofactor')
        source=source.replace('actual_ak_subgroup','actual_cofactor_subgroup')
        source=source.replace('subgroupOrder • represented = 0 ∧ represented ≠ 0','subgroupOrder • represented = 0')
        source=source.replace('represented, coordinates, subgroup, nonidentity','represented, coordinates, subgroup')
    return _signature_audits(source)


def generate_first_group_window(checked, extracted,
        arithmetic_module='RuntimeOwnershipWindowCandidate',
        arithmetic_namespace='RuntimeOwnershipWindow',namespace='RuntimeOwnershipFirstGroupWindow'):
    """Actual bit/row-to-group bridge; sender base-role source join stays explicit."""
    from .generate_hash_round import linear,_signature_audits
    if checked['metadata']['window_start']!=0:
        raise relation.RelationError('first group bridge requires global window zero')
    for name in (arithmetic_module,arithmetic_namespace,namespace):
        if not isinstance(name,str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',name):
            raise relation.RelationError('ownership group bridge module name')
    roles={role:entry['row'] for entry in extracted['templates'] for role in entry['roles']}
    rowmap={row['row']:row for row in extracted['selected_rows']}
    indices=[roles.get('bit.250'),roles.get('bit.251')]
    if any(i not in rowmap for i in indices):
        raise relation.RelationError('ownership group bridge missing actual bit rows')
    rows=[]
    for index,handle in zip(indices,checked['bits'][250:252]):
        row=rowmap[index];a=tuple((c,int(v,16)) for c,v in row['a']);b=tuple((c,int(v,16)) for c,v in row['b'])
        if a!=checked['derived'][handle] or b!=a:
            raise relation.RelationError('ownership group bridge wrong bit row')
        rows.append((a,b))
    A='ShielddSecurity.'+arithmetic_namespace
    source=f'''import ShielddSecurity.{arithmetic_module}
import ShielddSecurity.RuntimeTransferCurveParameters
import ShielddSecurity.ScalarBits
set_option maxHeartbeats 300000
namespace ShielddSecurity.{namespace}
def bitRows : List Row := [
'''+',\n'.join('  ⟨'+linear(a)+', '+linear(b)+'⟩' for a,b in rows)+f''']
def originalBitRows : List Nat := {indices}
def rawRows : List Row := {A}.rawRows ++ bitRows
theorem checked_bits : ScalarBits.checkBits {A}.modulus bitRows [{A}.low, {A}.high] = true := by decide

theorem actual_first_group_window {{F J : Type}} [Field F] [CharP F {A}.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (base : J)
    (baseRole : {A}.base rho = model.coordinates base)
    (satisfied : Satisfies rho rawRows) :
    {A}.result rho = model.coordinates
      (((ScalarBits.decodeBit rho {A}.low).toNat + 2 * (ScalarBits.decodeBit rho {A}.high).toNat) • base) := by
  have arith : Satisfies rho {A}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have bits : Satisfies rho bitRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  have lowValue := ScalarBits.checked_bit_value rho bitRows bits [{A}.low, {A}.high]
    checked_bits {A}.low (by simp)
  have highValue := ScalarBits.checked_bit_value rho bitRows bits [{A}.low, {A}.high]
    checked_bits {A}.high (by simp)
  rcases {A}.arithmetic_window rho one four arith with
    ⟨twiceRows, tripleRows, firstRows, secondRows, addRows, selected⟩
  rw [baseRole] at twiceRows tripleRows
  have parameters := RuntimeTransferCurveParameters.actual_curve_parameters codec
  have nonSquare : Group.NoUnitSquare ({A}.coefficientD : F) := parameters.1
  have imaginarySquare := parameters.2.1
  have precomputed := TransferOwnership.precompute_coordinates ({A}.coefficientD : F)
    (RuntimeJubjub.imaginary : F) model nonSquare imaginarySquare base
    ({A}.twice rho) ({A}.triple rho) twiceRows tripleRows
  have inputRole : {A}.input rho = model.coordinates 0 := by
    rw [model.identity]
    simp [{A}.input, eval, one, Group.identityPoint]
  rw [inputRole] at firstRows
  rw [selected, baseRole, precomputed.1, precomputed.2, lowValue, highValue] at addRows
  have result := TransferOwnership.window_coordinates ({A}.coefficientD : F)
    (RuntimeJubjub.imaginary : F) model nonSquare imaginarySquare (0 : J) base
    (ScalarBits.decodeBit rho {A}.low) (ScalarBits.decodeBit rho {A}.high)
    ({A}.first rho) ({A}.second rho) ({A}.result rho) firstRows secondRows addRows
  simpa only [smul_zero, zero_add] using result
#print axioms checked_bits
#print axioms actual_first_group_window
end ShielddSecurity.{namespace}
'''
    return _signature_audits(source)


def generate_window_equations(checked, extracted, metadata_hash, window_offset=0,
                              namespace='RuntimeOwnershipWindow', include_precompute=True):
    """Compose one window's checked polynomials and actual Div equations.

    The conclusion is arithmetic only. Boolean decoding, represented sender
    points, whole-trace membership and the final target remain later joins.
    """
    from .generate_group_cones import generate_checked
    from .generate_hash_round import linear, signed, _signature_audits
    from .group_rows import D
    cones=cone_certificates(checked,extracted,window_offset,include_precompute)
    quotients=quotient_certificates(checked,extracted,window_offset,include_precompute)
    if not isinstance(namespace,str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',namespace):
        raise relation.RelationError('ownership component namespace')
    digest=checked['metadata']['relation_digest'];cns=namespace+'Cones';qns=namespace+'Div'
    csource=generate_checked(cones,metadata_hash,digest,namespace=cns,full_audits=True)
    qsource=generate_quotient_boundaries(quotients,metadata_hash,digest,namespace=qns)
    # Both generated modules retain their own original-row conjunction; the
    # composition below restricts one arbitrary assignment to each conjunction.
    source='import ShielddSecurity.TransferOwnership\n'
    source+=csource.removeprefix('import ShielddSecurity.GroupWindows\n')
    source+=qsource.removeprefix('import ShielddSecurity.Compiler\n')
    prefix_source=source
    source=''
    C='ShielddSecurity.'+cns;Q='ShielddSecurity.'+qns
    definitions=re.findall(r'^def (\w+) : Linear :=',csource,re.M)
    def observed(value):
        return checked['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    window=checked['windows'][window_offset];points={**checked['points'],
        'input':window[0],'first':window[1],'second':window[2],
        'selected':window[3],'result':window[4]}
    source+=f'\nnamespace ShielddSecurity.{namespace}\ndef rawRows : List Row := {C}.rawRows ++ {Q}.rawRows\n'
    source+=f'def modulus : Nat := {relation.MODULUS}\ndef coefficientD : Int := {signed(D)}\n'
    for role in ('base','twice','triple','input','first','second','selected','result'):
        x,y=map(observed,points[role])
        source+=f'def {role} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(x)}, eval rho {linear(y)}⟩\n'
    bit_offset=2*(125-checked['metadata']['window_start']-window_offset)
    low,high=(checked['derived'][h] for h in checked['bits'][bit_offset:bit_offset+2])
    source+=f'def low : Linear := {linear(low)}\ndef high : Linear := {linear(high)}\n'
    source+=f'''theorem arithmetic_window {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    TransferOwnership.DoubleEquations (base rho) (twice rho) ∧
    TransferOwnership.AddEquations (coefficientD : F) (twice rho) (base rho) (triple rho) ∧
    TransferOwnership.DoubleEquations (input rho) (first rho) ∧
    TransferOwnership.DoubleEquations (first rho) (second rho) ∧
    TransferOwnership.AddEquations (coefficientD : F) (second rho) (selected rho) (result rho) ∧
    selected rho = Group.windowPoint (eval rho low) (eval rho high)
      (base rho) (twice rho) (triple rho) := by
  have cs : Satisfies rho {C}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have qs : Satisfies rho {Q}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
'''
    if not include_precompute:
        source=source.replace('    TransferOwnership.DoubleEquations (base rho) (twice rho) ∧\n'
            '    TransferOwnership.AddEquations (coefficientD : F) (twice rho) (base rho) (triple rho) ∧\n','')
        source=source.replace('  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩',
                              '  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩')
    point_defs='base, twice, triple, input, first, second, selected, result, coefficientD, low, high, Group.delta'
    groups=[(0,0),(4,2),(8+14*window_offset,4),(12+14*window_offset,6),(16+14*window_offset,8)]
    if not include_precompute:
        groups=[(formula,index-4) for formula,index in groups[2:]]
    for formula_start,equation_start in groups:
        for axis in range(2):
            numerator=cones['cones'][next(i for i,c in enumerate(cones['cones']) if c['role']=='formula'+str(formula_start+axis))]
            denominator=cones['cones'][next(i for i,c in enumerate(cones['cones']) if c['role']=='formula'+str(formula_start+2+axis))]
            cert=quotients['certificates'][equation_start+axis]
            simplify=', '.join(C+'.'+name for name in definitions
                              if name.startswith((numerator['role']+'_',denominator['role']+'_')))
            source+=f'''  · have n := {C}.{numerator['role']}_sound rho one cs
    have d := {C}.{denominator['role']}_sound rho one cs
    simp only [{simplify}] at n d
    have equation := {Q}.equation{equation_start+axis}_sound rho one four qs
    change eval rho {linear(cert['quotient'])} * eval rho {linear(cert['denominator'])} =
      eval rho {linear(cert['numerator'])} at equation
    rw [n] at equation
    try rw [d] at equation
    simp only [TransferOwnership.DoubleEquations, TransferOwnership.AddEquations, {point_defs}] at *
    simp only [eval, one] at equation ⊢ <;>
      (convert equation using 1 <;> ring)
'''
    source+='  · change Group.Point.mk _ _ = Group.Point.mk _ _\n    apply congrArg₂ Group.Point.mk\n'
    for axis in range(2):
        role='formula'+str(20+14*window_offset+axis)
        simplify=', '.join(C+'.'+name for name in definitions if name.startswith(role+'_'))
        source+=f'''    · have selectedFormula := {C}.{role}_sound rho one cs
      simp only [{simplify}] at selectedFormula
      simp only [{point_defs}, Group.windowPoint, Group.chooseCoordinate, eval, one] at selectedFormula ⊢ <;>
        (convert selectedFormula using 1 <;> ring)
'''
    source+='#print axioms arithmetic_window\nend ShielddSecurity.'+namespace+'\n'
    return prefix_source+_signature_audits(source)


def generate_sender_ownership_join():
    """Compose actual sender cofactor rows with the checked whole window trace."""
    from .generate_hash_round import _signature_audits
    source = """import ShielddSecurity.RuntimeTransferOwnership
import ShielddSecurity.RuntimeSenderDiversified
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeTransferSenderOwnership
open RuntimeTransferOwnership
def rawRows : List Row := RuntimeTransferOwnership.rawRows ++ RuntimeSenderDiversified.rawRows
theorem base_role {F : Type} [Field F] (rho : Nat → F) :
    RuntimeSenderDiversified.point rho = RuntimeTransferOwnership.base rho := by rfl
theorem actual_sender_ownership {F J : Type} [Field F]
    [CharP F RuntimeTransferOwnership.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ senderBase : J,
      model.coordinates senderBase = RuntimeTransferOwnership.base rho ∧
      RuntimeTransferAk.subgroupOrder • senderBase = 0 ∧ senderBase ≠ 0 ∧
      RuntimeTransferOwnership.target rho = model.coordinates
        (ShielddSecurity.binary (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits) • senderBase) := by
  have windowSat : Satisfies rho RuntimeTransferOwnership.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have baseSat : Satisfies rho RuntimeSenderDiversified.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  obtain ⟨senderBase, coordinates, subgroup, nonidentity⟩ :=
    RuntimeSenderDiversified.actual_subgroup model standardOrder rho one baseSat
  rw [base_role rho] at coordinates
  have ownership := RuntimeTransferOwnership.actual_ownership rho one four codec model
    senderBase coordinates.symm windowSat
  exact ⟨senderBase, coordinates, subgroup, nonidentity, ownership⟩
"""
    for name in ['base_role', 'actual_sender_ownership']:
        source += f'#print axioms {name}\n'
    source += 'end ShielddSecurity.RuntimeTransferSenderOwnership\n'
    return _signature_audits(source)


def generate_rnk_inverse_boundary(checked, extracted):
    """Prove the existing DH x-inverse assertion from its actual four rows."""
    from .generate_hash_round import linear, _signature_audits
    _validate_rnk_composition_extraction(checked,extracted)
    pairs=[pair for pair in extracted['products'] if pair['role']=='nonidentity']
    if len(pairs)!=1 or len(pairs[0]['rows'])!=3:
        raise relation.RelationError('RNK inverse requires exact materialized product/assertion')
    rowmap={row['row']:row for row in extracted['selected_rows']}
    copy=checked['metadata']['constant_copy']
    copy_lc=canonical([(0,1),(copy,-1)])
    copies=[row for row in rowmap.values() if
            tuple((c,int(v,16)) for c,v in row['a'])==copy_lc and row['b']==[]]
    if len(copies)!=1:
        raise relation.RelationError('RNK inverse constant-copy row missing')
    def observed(value):
        return checked['derived'][value[1]] if value[0]=='source' else canonical([(0,value[1])])
    x,y=map(observed,checked['points']['output'])
    inverse=observed(checked['nonidentity_inverse'])
    first,second,assertion=[rowmap[index] for index in pairs[0]['rows']]
    auxiliary=tuple((c,int(v,16)) for c,v in first['b'])
    plus=tuple((c,int(v,16)) for c,v in second['b'])
    output=canonical((c,v*pow(4,-1,relation.MODULUS)) for c,v in combine(plus,auxiliary,-1))
    if tuple((c,int(v,16)) for c,v in first['a'])!=combine(inverse,x,-1):
        raise relation.RelationError('RNK inverse exact operand orientation mismatch')
    if tuple((c,int(v,16)) for c,v in second['a'])!=combine(inverse,x):
        raise relation.RelationError('RNK inverse plus orientation mismatch')
    rows=[first,second,assertion,copies[0]]
    source=f'''import ShielddSecurity.ScalarComparisonBounds
import ShielddSecurity.GroupWindows
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeRnkInverse
-- Actual ordinary relation: {extracted['identity']['relation_digest']}
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {[row['row'] for row in rows]}
def rawRows : List Row := [
'''
    source+=',\n'.join('  ⟨'+linear(tuple((c,int(v,16)) for c,v in row['a']))+', '+
                      linear(tuple((c,int(v,16)) for c,v in row['b']))+'⟩' for row in rows)+']\n'
    source+=f'''def point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(x)}, eval rho {linear(y)}⟩
theorem inverse_equation {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho {linear(inverse)} * eval rho {linear(x)} = 1 := by
  have product := Compiler.checked_product_sound rho rawRows {linear(inverse)} {linear(x)}
    {linear(output)} {linear(auxiliary)} four satisfied (by decide) (by decide)
  have assertion := ScalarComparisonBounds.checked_equality rho rawRows satisfied
    {linear(output)} [( {copy},1)] (by decide)
  have copied := ScalarComparisonBounds.checked_equality rho rawRows satisfied
    [(0,1)] [({copy},1)] (by decide)
  rw [product] at assertion
  exact assertion.trans (copied.symm.trans (by simp [eval,one]))
theorem output_x_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho {linear(x)} ≠ 0 := by
  intro zero
  have equation := inverse_equation rho one four satisfied
  rw [zero,mul_zero] at equation
  exact zero_ne_one equation
theorem output_nonidentity {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : point rho ≠ Group.identityPoint := by
  intro same
  apply output_x_nonzero rho one four satisfied
  have x := congrArg Group.Point.x same
  simpa only [point,Group.identityPoint] using x
#print axioms inverse_equation
#print axioms output_x_nonzero
#print axioms output_nonidentity
end ShielddSecurity.RuntimeRnkInverse
'''
    return _signature_audits(source)


def rnk_inverse_controls(checked, extracted):
    """Two actual four-row assignments; excludes loop, IVK and hash constraints."""
    generate_rnk_inverse_boundary(checked,extracted)
    pair=next(pair for pair in extracted['products'] if pair['role']=='nonidentity')
    rowmap={row['row']:row for row in extracted['selected_rows']}
    copy=checked['metadata']['constant_copy']
    def unit(value):
        if value[0]!='source':
            raise relation.RelationError('RNK inverse control requires source coordinate')
        lc=checked['derived'][value[1]]
        if len(lc)!=1 or lc[0][1]!=1:
            raise relation.RelationError('RNK inverse control requires unit columns')
        return lc[0][0]
    x,y=map(unit,checked['points']['output']);inverse=unit(checked['nonidentity_inverse'])
    first,second,assertion=[rowmap[index] for index in pair['rows']]
    aux=first['b']
    output=canonical((c,v*pow(4,-1,relation.MODULUS)) for c,v in combine(
        tuple((c,int(v,16)) for c,v in second['b']),tuple((c,int(v,16)) for c,v in aux),-1))
    if len(aux)!=1 or int(aux[0][1],16)!=1 or len(output)!=1 or output[0][1]!=1:
        raise relation.RelationError('RNK inverse control product column shape')
    copies=[row for row in rowmap.values() if row['b']==[] and
            tuple((c,int(v,16)) for c,v in row['a'])==canonical([(0,1),(copy,-1)])]
    rows=[first,second,assertion,copies[0]]
    def failures(rho):
        def evaluate(terms):return sum(rho[c]*int(v,16) for c,v in terms)%relation.MODULUS
        return [row['row'] for row in rows if evaluate(row['a'])**2%relation.MODULUS!=evaluate(row['b'])]
    positive={0:1,copy:1,x:1,y:1,inverse:1,output[0][0]:1,aux[0][0]:0}
    mutant={0:1,copy:1,x:0,y:1,inverse:0,output[0][0]:0,aux[0][0]:0}
    if failures(positive)!=[] or failures(mutant)!=[assertion['row']] or mutant[x]!=0 or mutant[y]!=1:
        raise relation.RelationError('RNK inverse intended semantic omission not observed')
    return {'scope':'four actual RNK inverse/copy rows only; loop/cofactor/IVK/hash/full Transfer excluded',
            'selected_rows':[row['row'] for row in rows],
            'positive':{'assignment':sorted(positive.items()),'rejected_rows':[]},
            'assertion_omission':{'assignment':sorted(mutant.items()),'omitted_row':assertion['row'],
                                  'original_rejected_rows':[assertion['row']],
                                  'remaining_rows_satisfied':True,'point_is_identity':True}}


def generate_rnk_base_join():
    """Discharge the loop base role using its actual 74-row cofactor slice."""
    return (generate_sender_ownership_join()
            .replace('RuntimeTransferSenderOwnership', 'RuntimeTransferRnkBase')
            .replace('RuntimeSenderDiversified', 'RuntimeSenderRnkDh')
            .replace('RuntimeTransferOwnership', 'RuntimeTransferRnkLoop')
            .replace('RuntimeTransferRnkLoop.target rho', 'ShielddSecurity.RuntimeRnkTrace112.window13_output rho')
            .replace('actual_sender_ownership', 'actual_rnk_multiplication')
            .replace('RuntimeTransferRnkLoop.actual_ownership', 'RuntimeTransferRnkLoop.actual_multiplication'))


def generate_ivk_ownership_join():
    """Identify actual ownership bits with the same-assignment IVK reduction."""
    from .generate_hash_round import _signature_audits
    source = """import ShielddSecurity.RuntimeTransferSenderOwnership
import ShielddSecurity.RuntimeTransferIvk
import ShielddSecurity.Arithmetic
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferOwnershipIvk
def rawRows : List Row := RuntimeTransferSenderOwnership.rawRows ++ RuntimeTransferIvk.originalRows
theorem consumer_checked :
    Compiler.canonical RuntimeTransferOwnership.modulus
      (ScalarBits.bitLinear RuntimeTransferOwnership.bits) =
    Compiler.canonical RuntimeTransferOwnership.modulus RuntimeTransferReduction.consumer := by decide
theorem bits_checked : ScalarBits.checkBits RuntimeTransferOwnership.modulus
    RuntimeTransferOwnership.bitRows RuntimeTransferOwnership.bits = true := by decide
theorem decoded_scalar {F : Type} [Field F] [CharP F RuntimeTransferOwnership.modulus]
    (rho : Nat → F) (r : Nat) (bounded : r < Scalar.order)
    (consumer : (r : F) = eval rho RuntimeTransferReduction.consumer)
    (satisfied : Satisfies rho RuntimeTransferOwnership.bitRows) :
    ShielddSecurity.binary (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits) = r := by
  have value := ScalarBits.decoded_bits_value rho RuntimeTransferOwnership.bitRows satisfied
    RuntimeTransferOwnership.bits bits_checked
  have same := Compiler.canonical_equal rho (ScalarBits.bitLinear RuntimeTransferOwnership.bits)
    RuntimeTransferReduction.consumer consumer_checked
  have bitBound := ShielddSecurity.binary_bound (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits)
  have length : (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits).length = 252 := by rfl
  rw [length] at bitBound
  apply bounded_cast_injective (F := F) (p := Scalar.modulus)
    (lt_trans bitBound (by decide : 2^252 < Scalar.modulus))
    (lt_trans bounded (by decide : Scalar.order < Scalar.modulus))
  exact value.symm.trans (same.trans consumer.symm)
theorem actual_ivk_ownership {F J : Type} [Field F]
    [CharP F RuntimeTransferOwnership.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ q r : Nat, ∃ senderBase : J,
      q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧ q * Scalar.order + r < Scalar.modulus ∧
      ((q * Scalar.order + r : Nat) : F) =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          (RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho)) ∧
      model.coordinates senderBase = RuntimeTransferOwnership.base rho ∧
      RuntimeTransferAk.subgroupOrder • senderBase = 0 ∧ senderBase ≠ 0 ∧
      RuntimeTransferOwnership.target rho = model.coordinates (r • senderBase) := by
  have ownershipSat : Satisfies rho RuntimeTransferSenderOwnership.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inl member))
  have ivkSat : Satisfies rho RuntimeTransferIvk.originalRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  obtain ⟨q, r, qBound, positive, rBound, noWrap, qRole, rRole, hash, consumer⟩ :=
    RuntimeTransferIvk.actual_hash_reduction rho one four ivkSat
  have bitSat : Satisfies rho RuntimeTransferOwnership.bitRows := by
    intro row member
    apply ownershipSat row
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_append.mpr
    apply Or.inr
    exact List.mem_append.mpr (Or.inl member)
  have scalar := decoded_scalar rho r rBound consumer bitSat
  obtain ⟨senderBase, coordinates, subgroup, nonidentity, target⟩ :=
    RuntimeTransferSenderOwnership.actual_sender_ownership rho one four codec model standardOrder ownershipSat
  rw [scalar] at target
  exact ⟨q, r, senderBase, qBound, positive, rBound, noWrap, hash, coordinates, subgroup, nonidentity, target⟩
"""
    for name in ['consumer_checked', 'bits_checked', 'decoded_scalar', 'actual_ivk_ownership']:
        source += f'#print axioms {name}\n'
    source += 'end ShielddSecurity.RuntimeTransferOwnershipIvk\n'
    return _signature_audits(source)


def generate_rnk_ivk_join():
    """Identify the RNK loop's decoded scalar with the actual canonical IVK."""
    source = (generate_ivk_ownership_join()
              .replace('RuntimeTransferOwnershipIvk', 'RuntimeTransferRnkIvk')
              .replace('RuntimeTransferSenderOwnership', 'RuntimeTransferRnkBase')
              .replace('RuntimeTransferOwnership', 'RuntimeTransferRnkLoop')
              .replace('actual_ivk_ownership', 'actual_ivk_rnk')
              .replace('actual_sender_ownership', 'actual_rnk_multiplication')
              .replace('RuntimeTransferRnkLoop.target rho', 'ShielddSecurity.RuntimeRnkTrace112.window13_output rho'))
    # Loop rows append Boolean rows directly, without owner endpoint rows.
    source = source.replace('    exact List.mem_append.mpr (Or.inl member)\n  have scalar :=',
                            '    exact member\n  have scalar :=')
    return source


def joined_sender_endpoint_controls(chunks, extractions, template, substitutions):
    """Actual loop plus both cofactor row slices; excludes IVK and full Transfer."""
    controls = endpoint_controls(chunks, extractions)
    p = relation.MODULUS
    order = 6554484396890773809930967563523245729705921265872317281365359162392183254199
    d = -10240 * pow(10241, -1, p) % p
    def add(a, b):
        x, y = a; u, v = b; delta = d*x*u*y*v % p
        return ((x*v+y*u)*pow((1+delta)%p, -1, p)%p,
                (y*v+x*u)*pow((1-delta)%p, -1, p)%p)
    def multiply(point, scalar):
        result = (0, 1)
        while scalar:
            if scalar & 1: result = add(result, point)
            point = add(point, point); scalar >>= 1
        return result
    q = (3, 26155723652191673091881779851507865815856437797311909079256717375290769542325)
    preimages = [q, add(q,q)]
    preimages.append(add(preimages[-1], preimages[-1]))
    base = add(preimages[-1], preimages[-1])
    if multiply(base, order) != (0,1) or base[0] == 0:
        raise relation.RelationError('joined cofactor base predicate not observed')
    rows = {row['row']: row for row in template['selected_rows']}
    if len(rows) != 74:
        raise relation.RelationError('joined control requires complete cofactor template')
    def lc(terms, rho):
        return sum(rho[c] * int(v,16) for c,v in terms) % p
    copy_rows = [row for row in rows.values() if row['b'] == [] and len(row['a']) == 2
                 and row['a'][0] == [0, format(1,'064x')]
                 and int(row['a'][1][1],16) == p-1]
    if len(copy_rows) != 1:
        raise relation.RelationError('joined control constant-copy identity')
    copy_column = copy_rows[0]['a'][1][0]
    def cofactor_assignment(negative):
        rho = {0:1, copy_column:1, 1980:base[0],1981:base[1],1982:q[0],1983:q[1],
               1987:pow(base[0],-1,p)}
        for i,(x,y) in enumerate(preimages):
            delta = d*x*x*y*y % p
            rho[1984+i] = pow((1-delta*delta)%p,-1,p)
        if negative:
            for column in (1980,1982,1987):rho[column] = -rho[column] % p
        pending = list(rows.values())
        while pending:
            progress = False; waiting = []
            for row in pending:
                if any(c not in rho for c,_ in row['a']):waiting.append(row);continue
                unknown = [(c,int(v,16)) for c,v in row['b'] if c not in rho]
                if len(unknown) > 1:waiting.append(row);continue
                if unknown:
                    column,coefficient = unknown[0]
                    known = sum(rho[c]*int(v,16) for c,v in row['b'] if c in rho)
                    rho[column] = (lc(row['a'],rho)**2-known)*pow(coefficient,-1,p)%p
                if lc(row['a'],rho)**2%p != lc(row['b'],rho):
                    raise relation.RelationError('joined cofactor assignment row failure')
                progress = True
            if not progress:raise relation.RelationError('joined cofactor assignment unresolved columns')
            pending = waiting
        return rho
    positive = cofactor_assignment(False); negative = cofactor_assignment(True)
    by_name = {item['namespace']:item for item in substitutions}
    if set(by_name) != {'RuntimeSenderDiversified','RuntimeSenderTransmission'}:
        raise relation.RelationError('joined control requires both sender point substitutions')
    all_rows = {}
    for extracted in extractions + substitutions:
        for row in extracted['selected_rows']:
            if row['row'] in all_rows and all_rows[row['row']] != row:
                raise relation.RelationError('joined control raw row conflict')
            all_rows[row['row']] = row
    result = []
    for case in controls['cases']:
        rho = dict(case['assignment'])
        for name in ('RuntimeSenderDiversified','RuntimeSenderTransmission'):
            mapping = dict(by_name[name]['columns'])
            assignment = negative if name == 'RuntimeSenderTransmission' and case['omitted_original_row'] is not None else positive
            for column,value in assignment.items():
                target = mapping[column]
                if target in rho and rho[target] != value:
                    raise relation.RelationError('joined control shared assignment conflict')
                rho[target] = value
        rejected = [index for index,row in sorted(all_rows.items())
                    if lc(row['a'],rho)**2%p != lc(row['b'],rho)]
        expected = [] if case['omitted_original_row'] is None else [case['omitted_original_row']]
        if rejected != expected:
            raise relation.RelationError('joined endpoint intended failure not observed')
        target = (rho[1512],rho[1513]); output = (rho[3007],rho[3008])
        x,y = target
        if (y*y-x*x-1-d*x*x*y*y)%p or x == 0 or multiply(target,order)!=(0,1):
            raise relation.RelationError('joined target group predicate not observed')
        if output != base or (target == output) != (not expected):
            raise relation.RelationError('joined violated ownership predicate not observed')
        result.append({**case,'assignment':sorted(rho.items()),'original_rejected_rows':rejected,
                       'both_sender_cofactor_slices_satisfied':True,
                       'retained_selected_rows_satisfied':True})
    return {'scope':f'actual {len(all_rows)}-row ownership loop plus both sender cofactor controls; IVK hash/reduction and all other Transfer constraints excluded',
            'cases':result}


def generate_authorization_ownership_projection():
    """Partial independent semantic projection; other authorization clauses stay open."""
    from .generate_hash_round import _signature_audits
    source = """import ShielddSecurity.RuntimeTransferOwnershipIvk
import ShielddSecurity.RuntimeTransferAuthorizationAk
import ShielddSecurity.RuntimeSenderTransmission
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferAuthorizationOwnership
open RuntimeTransferAuthorizationAk
noncomputable def projection {F : Type} [Field F]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (base : TransferSem.Witness) : TransferSem.Witness :=
    let scalar := RuntimeTransferAuthorization.scalar_projection codec rho base
    { scalar with sender := { scalar.sender with address :=
        { diversified := decodePoint codec (RuntimeTransferOwnership.base rho),
          transmission := decodePoint codec (RuntimeTransferOwnership.target rho) } } }
def originalRows : List Row := RuntimeTransferOwnershipIvk.rawRows ++
    (RuntimeTransferAuthorizationAk.originalRows ++ RuntimeSenderTransmission.rawRows)
theorem transmission_role {F : Type} [Field F] (rho : Nat → F) :
    RuntimeSenderTransmission.point rho = RuntimeTransferOwnership.target rho := by rfl
theorem projected_authorization_owner {F J : Type} [Field F]
    [CharP F RuntimeTransferOwnership.modulus] [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (c : TransferSem.Crypto)
    (base : TransferSem.Witness) (rho : Nat → F)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (subgroupInterpreter : ∀ represented : J, RuntimeTransferAk.subgroupOrder • represented = 0 →
      c.subgroup (decodePoint codec (model.coordinates represented)))
    (hashInterpreter : ∀ nk ax ay : Nat,
      nk < Scalar.modulus → ax < Scalar.modulus → ay < Scalar.modulus →
      c.hash .incomingViewingKey [nk,ax,ay] = codec.decode
        (Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          [(nk : F),(ax : F),(ay : F)]))
    (multiplyInterpreter : ∀ scalar : Nat, ∀ represented : J,
      scalar < Scalar.order → RuntimeTransferAk.subgroupOrder • represented = 0 →
      c.mul scalar (decodePoint codec (model.coordinates represented)) =
        decodePoint codec (model.coordinates (scalar • represented)))
    (one : rho 0 = 1) (satisfied : Satisfies rho originalRows) :
    let w := projection codec rho base
    TransferSem.AuthorizationScalarSem c w ∧ TransferSem.ValidPoint c w.auth.ak ∧
      TransferSem.nonidentity w.auth.ak ∧
      TransferSem.ValidPoint c w.sender.address.diversified ∧
      TransferSem.nonidentity w.sender.address.diversified ∧
      TransferSem.ValidPoint c w.sender.address.transmission ∧
      TransferSem.nonidentity w.sender.address.transmission ∧
      c.mul w.auth.ivk w.sender.address.diversified = w.sender.address.transmission := by
  let w := projection codec rho base
  have ownerIvkSat : Satisfies rho RuntimeTransferOwnershipIvk.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inl member))
  have akSat : Satisfies rho RuntimeTransferAuthorizationAk.originalRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
  have transmissionSat : Satisfies rho RuntimeSenderTransmission.rawRows := by
    intro row member; exact satisfied row (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member))))
  have ownerSat : Satisfies rho RuntimeTransferSenderOwnership.rawRows := by
    intro row member; exact ownerIvkSat row (List.mem_append.mpr (Or.inl member))
  have bitSat : Satisfies rho RuntimeTransferOwnership.bitRows := by
    intro row member
    exact ownerSat row (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))))
  have four := RuntimeTransferAkCones.fourNonzero (F := F)
  have ak := RuntimeTransferAuthorizationAk.projected_authorization_ak codec c base rho model
    standardOrder subgroupInterpreter hashInterpreter one akSat
  have numeric : TransferSem.AuthorizationScalarSem c w := ak.1
  obtain ⟨senderBase, baseCoordinates, baseSubgroup, baseNonzero, ownerTarget⟩ :=
    RuntimeTransferSenderOwnership.actual_sender_ownership rho one four codec model standardOrder ownerSat
  obtain ⟨senderTarget, targetCoordinates, targetSubgroup, targetNonzero⟩ :=
    RuntimeSenderTransmission.actual_subgroup model standardOrder rho one transmissionSat
  rw [transmission_role rho] at targetCoordinates
  have bitValue := ScalarBits.decoded_bits_value rho RuntimeTransferOwnership.bitRows bitSat
    RuntimeTransferOwnership.bits RuntimeTransferOwnershipIvk.bits_checked
  have consumer := Compiler.canonical_equal rho (ScalarBits.bitLinear RuntimeTransferOwnership.bits)
    RuntimeTransferReduction.consumer RuntimeTransferOwnershipIvk.consumer_checked
  have encoded := bitValue.symm.trans consumer
  have binaryBound := ShielddSecurity.binary_bound (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits)
  have length : (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits).length = 252 := by rfl
  rw [length] at binaryBound
  have scalarRole : w.auth.ivk = ShielddSecurity.binary
      (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits) := by
    change codec.decode (eval rho RuntimeTransferReduction.consumer) = _
    rw [← encoded]
    exact TransferReduction.decode_canonical_cast codec _
      (lt_trans binaryBound (by decide : 2^252 < Scalar.modulus))
  have baseValid : TransferSem.ValidPoint c w.sender.address.diversified := by
    change TransferSem.ValidPoint c (decodePoint codec (RuntimeTransferOwnership.base rho))
    rw [← baseCoordinates]
    exact ⟨⟨codec.bounded _,codec.bounded _⟩,subgroupInterpreter senderBase baseSubgroup⟩
  have targetValid : TransferSem.ValidPoint c w.sender.address.transmission := by
    change TransferSem.ValidPoint c (decodePoint codec (RuntimeTransferOwnership.target rho))
    rw [← targetCoordinates]
    exact ⟨⟨codec.bounded _,codec.bounded _⟩,subgroupInterpreter senderTarget targetSubgroup⟩
  have baseNonidentity : TransferSem.nonidentity w.sender.address.diversified := by
    change TransferSem.nonidentity (decodePoint codec (RuntimeTransferOwnership.base rho))
    rw [← baseCoordinates]
    exact decoded_nonidentity codec _ model senderBase baseNonzero
  have targetNonidentity : TransferSem.nonidentity w.sender.address.transmission := by
    change TransferSem.nonidentity (decodePoint codec (RuntimeTransferOwnership.target rho))
    rw [← targetCoordinates]
    exact decoded_nonidentity codec _ model senderTarget targetNonzero
  have owner := multiplyInterpreter w.auth.ivk senderBase numeric.1 baseSubgroup
  rw [scalarRole,baseCoordinates,← ownerTarget] at owner
  rw [← scalarRole] at owner
  exact ⟨numeric,ak.2.1,ak.2.2,baseValid,baseNonidentity,targetValid,targetNonidentity,owner⟩
"""
    for name in ['transmission_role', 'projected_authorization_owner']:
        source += f'#print axioms {name}\n'
    source += 'end ShielddSecurity.RuntimeTransferAuthorizationOwnership\n'
    return _signature_audits(source)
