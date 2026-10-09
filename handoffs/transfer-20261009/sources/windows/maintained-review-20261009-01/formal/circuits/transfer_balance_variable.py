"""Strict balance129 variable-loop ingress; no quotient truth from source handles.

This separate schema preserves the reviewed252bit ownership schema unchanged.
Actual original-row extraction and group legality remain subsequent obligations.
"""
import hashlib,re
from . import transfer_relation as relation,transfer_ownership as ownership
from .transfer_balance_rows import canonical,combine,source_index

SCOPE='bounded balance129 variable-loop observation; actual row/group/native joins open'


def inspect_metadata(data,expected_relation,expected_signed,expected_base):
    return _inspect_metadata(data,expected_relation,expected_signed,expected_base)


def _inspect_metadata(data,expected_relation,expected_signed,expected_base,qualification_parent_sha256=None):
    if not isinstance(data,bytes) or len(data)>2*1024*1024:
        raise relation.RelationError('balance variable metadata exceeds2MiB')
    if not isinstance(expected_relation,str) or not re.fullmatch('[0-9a-f]{64}',expected_relation):
        raise relation.RelationError('exact balance variable relation digest required')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','window_start','window_count','total_windows',
        'bit_width','negative','magnitude','base','twice','triple','bits','output','precompute_quotients','windows','expressions','nodes'}
    if set(obj)!=keys or obj['schema']!='shieldd-transfer-balance-variable-v1' or obj['family']!='transfer' or obj['scope']!=SCOPE:
        raise relation.RelationError('unknown balance variable closed schema/scope')
    wanted=False if qualification_parent_sha256 is not None else True
    if obj['relation_digest']!=expected_relation or obj['ordinary_full_ordered_rows_equal'] is not wanted or obj['repeated_observations_equal'] is not wanted:
        raise relation.RelationError('balance variable full ordinary/repeat qualification required')
    domain=relation.natural(obj['domain_size']);full=relation.natural(obj['full_rows']);copy=relation.natural(obj['constant_copy'],domain)
    if domain<4 or domain&(domain-1) or not 0<full<=domain or copy<3:
        raise relation.RelationError('balance variable relation bounds')
    start=relation.natural(obj['window_start'],65);count=relation.natural(obj['window_count'],17)
    if not 1<=count<=16 or start+count>65 or type(obj['total_windows'])is not int or obj['total_windows']!=65 or type(obj['bit_width'])is not int or obj['bit_width']!=129:
        raise relation.RelationError('balance variable65/16/129 bounds')
    if not isinstance(obj['bits'],list) or len(obj['bits'])!=129:
        raise relation.RelationError('balance variable exact129 source bits')
    bits=tuple(source_index(bit) for bit in obj['bits'])
    if len(set(bits))!=129 or any(tag!=1 for tag,_ in bits):
        raise relation.RelationError('balance variable distinct witness bits required')
    if (not isinstance(expected_signed,dict) or expected_signed.get('identity',{}).get('relation_digest')!=expected_relation or
        expected_signed.get('copy')!=copy or expected_signed.get('bits')!=[index+3 for _,index in bits]):
        raise relation.RelationError('balance variable exact checked signed parent bit/link identity required')
    roots=set(bits)
    def observed(value,collect=True):
        if not isinstance(value,dict) or len(value)!=1:
            raise relation.RelationError('balance variable observed shape')
        if set(value)=={'source'}:
            handle=source_index(value['source'])
            if handle[0]==1 and handle[1]+3>=domain:
                raise relation.RelationError('balance variable witness outside domain')
            if collect:roots.add(handle)
            return ('source',handle)
        if set(value)=={'native'} and isinstance(value['native'],str) and re.fullmatch('[0-9a-f]{64}',value['native']):
            number=int(value['native'],16)
            if number<relation.MODULUS:return ('native',number)
        raise relation.RelationError('balance variable noncanonical observed value')
    def point(values):
        if not isinstance(values,list) or len(values)!=2:raise relation.RelationError('balance variable point shape')
        return tuple(observed(value) for value in values)
    negative=observed(obj['negative']);magnitude=observed(obj['magnitude'])
    if negative!=('source',(1,expected_signed.get('negative',-1)-3)) or magnitude!=('source',(1,expected_signed.get('magnitude',-1)-3)):
        raise relation.RelationError('balance variable shared signed witness roles')
    points={key:point(obj[key]) for key in ('base','twice','triple','output')}
    if not isinstance(expected_base,list) or len(expected_base)!=2 or points['base']!=tuple(observed(value,False) for value in expected_base):
        raise relation.RelationError('balance variable actual asset-generator source role mismatch')
    def quotient(values):
        if not isinstance(values,list) or len(values)!=6:raise relation.RelationError('balance variable quotient shape')
        return tuple(observed(value) for value in values)
    if not isinstance(obj['precompute_quotients'],list) or len(obj['precompute_quotients'])!=2:
        raise relation.RelationError('balance variable two shared precompute quotients')
    quotients=[quotient(value) for value in obj['precompute_quotients']]
    if quotients[0][4:]!=points['twice'] or quotients[1][4:]!=points['triple']:
        raise relation.RelationError('balance variable shared quotient table roles')
    if not isinstance(obj['windows'],list) or len(obj['windows'])!=count:
        raise relation.RelationError('balance variable window count')
    windows=[];window_bits=[]
    for offset,raw in enumerate(obj['windows']):
        index=start+offset
        if (not isinstance(raw,dict) or set(raw)!={'index','points','bits','quotients'} or type(raw['index'])is not int or raw['index']!=index or
            not isinstance(raw['points'],list) or len(raw['points'])!=5 or not isinstance(raw['bits'],list) or len(raw['bits'])!=2 or
            not isinstance(raw['quotients'],list) or len(raw['quotients'])!=3):
            raise relation.RelationError('balance variable exact indexed window shape')
        parsed=tuple(point(value) for value in raw['points']);pair=tuple(observed(value) for value in raw['bits'])
        low=128-2*index
        wanted=(('source',bits[low]),('native',0) if index==0 else ('source',bits[low+1]))
        if pair!=wanted:raise relation.RelationError('balance variable reversed bits/nativefalse high padding mismatch')
        if windows and parsed[0]!=windows[-1][4]:raise relation.RelationError('balance variable point chain mismatch')
        current=[quotient(value) for value in raw['quotients']]
        if tuple(q[4:] for q in current)!=(parsed[1],parsed[2],parsed[4]):
            raise relation.RelationError('balance variable quotient output roles')
        windows.append(parsed);window_bits.append(pair);quotients.extend(current)
    if start==0 and windows[0][0]!=(('native',0),('native',1)):
        raise relation.RelationError('balance variable initial identity required')
    if start+count==65 and windows[-1][4]!=points['output']:
        raise relation.RelationError('balance variable final output role')
    if not isinstance(obj['expressions'],list) or not 1<=len(obj['expressions'])<=4096:
        raise relation.RelationError('balance variable LC4096 bound')
    expressions={};previous=(-1,-1);term_count=0
    for item in obj['expressions']:
        if not isinstance(item,dict) or set(item)!={'source','terms'}:raise relation.RelationError('balance variable LC shape')
        source=source_index(item['source']);relation.terms(item['terms'],domain)
        if source<=previous:raise relation.RelationError('balance variable LC order')
        previous=source;term_count+=len(item['terms'])
        if term_count>65536:raise relation.RelationError('balance variable LC total term bound')
        terms=tuple((column,int(value,16)) for column,value in item['terms'])
        if any(column==copy for column,_ in terms) or (source[0]==0 and any(column!=0 for column,_ in terms)):
            raise relation.RelationError('balance variable pre-outline constant LC')
        if source[0]==1 and terms!=((source[1]+3,1),):raise relation.RelationError('balance variable witness LC identity')
        expressions[source]=terms
    if not roots<=set(expressions):raise relation.RelationError('balance variable missing role LC')
    if not isinstance(obj['nodes'],list) or len(obj['nodes'])>8192:raise relation.RelationError('balance variable node8192 bound')
    nodes={};previous=-1
    for item in obj['nodes']:
        if not isinstance(item,dict) or set(item)!={'index','multiply','left','right'}:raise relation.RelationError('balance variable node shape')
        index=relation.natural(item['index'],2**32);left,right=source_index(item['left']),source_index(item['right'])
        if index<=previous or type(item['multiply'])is not bool or any(tag==2 and child>=index for tag,child in (left,right)):
            raise relation.RelationError('balance variable source topology')
        previous=index;nodes[(2,index)]=(item['multiply'],left,right)
    boundaries={value[1] for point in (points['base'],windows[0][0]) for value in point if value[0]=='source'}
    if start+count<65:boundaries.update(value[1] for value in points['output'] if value[0]=='source')
    pending=list(roots);visited=set();required=set(roots)
    while pending:
        source=pending.pop()
        if source in visited:continue
        visited.add(source)
        if len(visited)>8192:raise relation.RelationError('balance variable source cone bound')
        if source[0]==2:
            if source not in nodes:raise relation.RelationError('balance variable missing source node')
            multiply,left,right=nodes[source]
            if source in boundaries:continue
            if multiply and left[0]!=0 and right[0]!=0:required.update((source,left,right))
            pending.extend((left,right))
        else:required.add(source)
    if set(nodes)!={source for source in visited if source[0]==2} or set(expressions)!=required:
        raise relation.RelationError('balance variable missing/extra source graph or LC')
    derived={}
    for source in sorted(visited):
        if source[0]!=2 or source in boundaries:derived[source]=expressions[source];continue
        multiply,left,right=nodes[source];value=None
        if not multiply:value=combine(derived[left],derived[right])
        else:
            for const,other in ((derived[left],derived[right]),(derived[right],derived[left])):
                if all(column==0 for column,_ in const):
                    factor=const[0][1] if const else 0;value=canonical((c,n*factor) for c,n in other);break
            if value is None:value=expressions[source]
        if source in expressions and value!=expressions[source]:raise relation.RelationError('balance variable source affine LC mismatch')
        derived[source]=value
    return dict(metadata=obj,metadata_sha256=hashlib.sha256(data).hexdigest(),signed_parent_metadata_sha256=expected_signed.get('metadata_sha256'),
        points=points,windows=windows,window_bits=window_bits,quotients=quotients,bits=bits,negative=negative,magnitude=magnitude,
        expressions=expressions,nodes=nodes,derived=derived,boundaries=boundaries,
        qualification_parent_sha256=qualification_parent_sha256,
        scope='closed local source/LC cone with exact role boundaries; prior asset/window and quotient/curve/original-row constructive transport OPEN')


def inspect_pages(qualified_parent,raw_pages,expected_relation,expected_signed,expected_base):
    """Derivative typed views retain each raw page's FALSE flags and identity.

    The actual qualifier has independently compared ordinary2+repeat rows and
    every page byte. This parser checks its closed descriptor/source joins;
    source-generation callers must still independently replay original rows.
    """
    import blake3
    if not isinstance(qualified_parent,bytes) or len(qualified_parent)>32768:
        raise relation.RelationError('balance variable pages parent32768 bound')
    parent=relation.record(qualified_parent)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','pages'}
    if (set(parent)!=keys or parent['schema']!='shieldd-transfer-balance-variable-pages-v1' or
        parent['family']!='transfer' or parent['scope']!='5 bounded balance129 window pages from one lowering; group/native joins open' or
        parent['relation_digest']!=expected_relation or parent['ordinary_full_ordered_rows_equal'] is not True or
        parent['repeated_observations_equal'] is not True or not isinstance(parent['pages'],list) or len(parent['pages'])!=5 or
        not isinstance(raw_pages,list) or len(raw_pages)!=5):
        raise relation.RelationError('balance variable qualified exactfive pages parent required')
    digest=hashlib.sha256(qualified_parent).hexdigest();chunks=[]
    for ordinal,(descriptor,data) in enumerate(zip(parent['pages'],raw_pages)):
        start,count=16*ordinal,min(16,65-16*ordinal)
        if (not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','window_start','window_count','blake3'} or
            any(type(descriptor[key])is not int or descriptor[key]!=value for key,value in
                (('ordinal',ordinal),('window_start',start),('window_count',count))) or
            not isinstance(data,bytes) or not 0<len(data)<=2*1024*1024 or
            descriptor['blake3']!=blake3.blake3(data).hexdigest()):
            raise relation.RelationError('balance variable page descriptor/order/byte identity')
        checked=_inspect_metadata(data,expected_relation,expected_signed,expected_base,digest)
        metadata=checked['metadata']
        if metadata['window_start']!=start or metadata['window_count']!=count or any(
            metadata[key]!=parent[key] for key in ('relation_digest','domain_size','full_rows','constant_copy')):
            raise relation.RelationError('balance variable raw page qualified-parent identity')
        chunks.append(checked)
    joined=join_chunks(chunks)
    return dict(parent=parent,parent_sha256=digest,chunks=chunks,joined=joined,
        raw_page_sha256=[hashlib.sha256(data).hexdigest() for data in raw_pages],
        scope='Derivative fivepage views retaining originalFALSE pending flags; independent fullrow replay and constructive group/native joins OPEN')


def match_formulas(checked):
    """Exact existing optimized formulas, including first high nativefalse."""
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
        graph,roles=ownership.expected_formula(kind,axis,inputs)
        if output[0]=='native':
            if graph['arity'] or graph['nodes'][graph['output']]!={'kind':'constant','value':output[1]}:
                raise relation.RelationError('balance variable native formula mismatch')
            pairs=[]
        else:
            # Each formula has its own declared input cut. Retain the actual
            # boundary node operation/ref record; do not fabricate a Witness.
            input_names=[name(role) for role in roles];local={};pending=[name(output[1])]
            while pending:
                current=pending.pop()
                if current in local:continue
                if current not in source:raise relation.RelationError('balance variable formula crosses unowned source boundary')
                local[current]=source[current]
                if current not in input_names and source[current]['kind'] in ('add','mul'):
                    pending.extend((source[current]['left'],source[current]['right']))
            for current in input_names:
                if current not in source:raise relation.RelationError('balance variable missing formula source input')
                local[current]=source[current]
            try:pairs=poseidon_graph.match_source(graph,local,input_names,name(output[1]))
            except ValueError as error:raise relation.RelationError('balance variable '+kind+'.'+axis+' source mismatch: '+str(error)) from error
        cones.append(dict(kind=kind,axis=axis,inputs=inputs,output=output,graph=graph,pairs=pairs))
    def quotient(kind,inputs,q):
        for offset,part in ((0,'numerator'),(2,'denominator')):
            for index,axis in enumerate(('x','y')):match(kind+'.'+part,axis,inputs,q[offset+index])
    points=checked['points'];quotients=checked['quotients']
    quotient('double',points['base'],quotients[0]);quotient('add',points['twice']+points['base'],quotients[1])
    for offset,window in enumerate(checked['windows']):
        first,second,third=quotients[2+3*offset:5+3*offset]
        quotient('double',window[0],first);quotient('double',window[1],second);quotient('add',window[2]+window[3],third)
        inputs=points['base']+points['twice']+points['triple']+checked['window_bits'][offset]
        for axis,output in zip(('x','y'),window[3]):match('select',axis,inputs,output)
    return dict(cones=cones,source=source,scope='exact local source formula correspondence; no quotient witness/division/curve/row premise derived')


def row_requirements(checked,expected_relation,*,include_bits=False):
    """Pure original node/quotient requirements after exact source matching.

    Variable divisions create a quotient-times-denominator product plus a
    numerator assertion. Both are matched; a quotient source handle itself
    never supplies the inverse or quotient equation.
    """
    match_formulas(checked)
    metadata=checked['metadata'];copy=metadata['constant_copy'];p=relation.MODULUS
    if metadata['relation_digest']!=expected_relation:
        raise relation.RelationError('balance variable original row identity mismatch')
    if type(include_bits)is not bool:raise relation.RelationError('balance variable bit extraction flag')
    derived=checked['derived']
    def outline(lc):return canonical((copy if c==0 else c,v) for c,v in lc)
    def observed(value):return derived[value[1]] if value[0]=='source' else canonical([(0,value[1])])
    required={(canonical([(0,1),(copy,p-1)]),()):['constant-copy']};products=[];squares=[]
    def require(role,left,right=()):required.setdefault((outline(left),outline(right)),[]).append(role)
    if include_bits:
        selected_bits={value[1] for pair in checked['window_bits'] for value in pair if value[0]=='source'}
        for bit in sorted(selected_bits):require('bit.'+str(bit[1]),derived[bit],derived[bit])
    for source,(multiply,left,right) in checked['nodes'].items():
        if source in checked.get('boundaries',set()):continue
        if not multiply or left[0]==0 or right[0]==0:continue
        a,b,out=derived[left],derived[right],derived[source];role='node.'+str(source[1])
        folded=next(((lc,other) for lc,other in ((a,b),(b,a)) if not lc or len(lc)==1 and lc[0][0]==0),None)
        if folded is not None:
            const,other=folded;factor=const[0][1] if const else 0
            if out!=canonical((c,v*factor) for c,v in other):raise relation.RelationError('balance variable folded source product LC mismatch')
            continue
        if a==b:require(role+'.square',a,out)
        else:products.append((role,outline(combine(a,b,-1)),outline(combine(a,b)),outline(out),None))
    for ordinal,quotient in enumerate(checked['quotients']):
        for axis in range(2):
            numerator,denominator,q=map(observed,(quotient[axis],quotient[axis+2],quotient[axis+4]))
            role='quotient.'+str(ordinal)+'.'+str(axis)
            constant=next(((lc,other) for lc,other in ((denominator,q),(q,denominator)) if not lc or len(lc)==1 and lc[0][0]==0),None)
            if constant is not None:
                const,other=constant;factor=const[0][1] if const else 0
                equation=combine(canonical((c,v*factor) for c,v in other),numerator,-1)
                if equation:require(role+'.assertion',equation)
            elif q==denominator:squares.append((role,outline(q),outline(numerator)))
            else:products.append((role,outline(combine(q,denominator,-1)),outline(combine(q,denominator)),None,outline(numerator)))
    return required,products,squares


def extract_rows(checked,stream,expected_relation,*,include_bits=False):
    """Full ordered replay; default requirement and returned bytes unchanged."""
    required,products,squares=row_requirements(checked,expected_relation,include_bits=include_bits)
    metadata=checked['metadata']
    from .transfer_arithmetic import extract_templates
    result=extract_templates(stream,expected_relation,metadata['domain_size'],metadata['full_rows'],required,products,squares,label='balance-variable')
    result.update(metadata_sha256=checked['metadata_sha256'],signed_parent_metadata_sha256=checked['signed_parent_metadata_sha256'],
        scope='actual bounded original product/auxiliary/quotient-assertion rows only; group legality and constructive sequencing OPEN')
    return result


def join_chunks(chunks):
    """Exact shared source/LC joins; no hash-only recurrence or witness claim."""
    if not isinstance(chunks,list) or not 1<=len(chunks)<=65:raise relation.RelationError('balance variable chunk collection')
    first=chunks[0];next_window=0;previous=None;common={};common_nodes={}
    keys=('schema','scope','relation_digest','domain_size','full_rows','constant_copy','total_windows','bit_width',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','negative','magnitude','base','twice','triple','bits','output','precompute_quotients')
    for chunk in chunks:
        if chunk.get('qualification_parent_sha256')!=first.get('qualification_parent_sha256'):
            raise relation.RelationError('balance variable qualification parent mismatch')
        metadata=chunk['metadata']
        if any(metadata[key]!=first['metadata'][key] for key in keys):raise relation.RelationError('balance variable shared parent/table/source mismatch')
        if metadata['window_start']!=next_window or len(chunk['windows'])!=metadata['window_count']:
            raise relation.RelationError('balance variable omit/reorder/duplicate windows')
        if chunk['signed_parent_metadata_sha256']!=first['signed_parent_metadata_sha256']:
            raise relation.RelationError('balance variable signed parent identity mismatch')
        if previous is not None and chunk['windows'][0][0]!=previous:
            raise relation.RelationError('balance variable cross-chunk point source chain')
        if chunk['quotients'][:2]!=first['quotients'][:2]:raise relation.RelationError('balance variable shared precompute source mismatch')
        for source,value in chunk['expressions'].items():
            if source in common and common[source]!=value:raise relation.RelationError('balance variable shared LC mismatch')
            common[source]=value
        for source,value in chunk['nodes'].items():
            if source in common_nodes and common_nodes[source]!=value:raise relation.RelationError('balance variable shared source node mismatch')
            common_nodes[source]=value
        previous=chunk['windows'][-1][4];next_window+=metadata['window_count']
    if next_window!=65 or first['windows'][0][0]!=(('native',0),('native',1)) or previous!=first['points']['output']:
        raise relation.RelationError('balance variable full65 endpoint coverage')
    return dict(windows=65,chunks=len(chunks),metadata_sha256=[chunk['metadata_sha256'] for chunk in chunks],
        signed_parent_metadata_sha256=first['signed_parent_metadata_sha256'],
        source_nodes=len(common_nodes),source_lcs=len(common),scope='exact full65 source/LC continuity only; actual original rows/native/group/completion joins OPEN')
