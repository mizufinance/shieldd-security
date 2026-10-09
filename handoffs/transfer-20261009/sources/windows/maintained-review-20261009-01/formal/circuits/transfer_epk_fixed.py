"""Actual fixed EPK source ingress; recovery is linked to independently typed74 roles.

This schema is distinct from spend's fixed loop. No scalar/point/inverse or row
truth is inferred from a source handle or page digest. Encryption role ingress
must be supplied separately once its broad capture is qualified.
"""
import hashlib
from . import transfer_relation as relation, transfer_fixed_spend as fixed
from .transfer_balance_rows import canonical,combine,source_index

SCOPE='bounded fixed EPK source roles; row/native claims open'
PARENT_SCOPE='8 bounded fixed EPK pages from one lowering; row/native claims open'
ALL_PARENT_SCOPE='48 bounded fixed EPK pages for six ordered scopes from one lowering; row/native claims open'
IDENTITY=('relation_digest','domain_size','full_rows','constant_copy')


def _qualified_caller_identity(accepted_roles,parent):
    """Use the accepted authorization ABI; its qualification has no repeat flag.

    The EPK48 parent independently requires repeated observations. Caller roles
    carry their own full ordinary-row qualification and typed IVK/RNK LC joins.
    """
    if not isinstance(accepted_roles,dict) or not isinstance(accepted_roles.get('observed'),dict):
        raise relation.RelationError('EPK all independently typed caller required')
    caller=accepted_roles.get('metadata',{})
    if (not isinstance(caller,dict) or caller.get('schema')!='shieldd-transfer-authorization-roles-v1' or
        caller.get('family')!='transfer' or caller.get('ordinary_full_ordered_rows_equal') is not True or
        'repeated_observations_equal' in caller or any(caller.get(k)!=parent[k] for k in IDENTITY) or
        not isinstance(caller.get('spend'),dict)):
        raise relation.RelationError('EPK all actual typed caller identity/qualification ABI')
    return caller


def inspect_recovery_page(data,accepted_capsules,accepted_roles):
    return _inspect_recovery_page(data,accepted_capsules,accepted_roles)


def _inspect_recovery_page(data,accepted_capsules,accepted_roles,qualification_parent_sha256=None):
    return _inspect_page_source(data,accepted_capsules,accepted_roles,qualification_parent_sha256)


def _inspect_page_source(data,accepted_capsules,accepted_roles,qualification_parent_sha256=None,source_only=False):
    if not isinstance(data,bytes) or not 0<len(data)<=2*1024*1024:
        raise relation.RelationError('EPK fixed page byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','lane','slot','window_start','window_count',
        'total_windows','bit_width','base','randomizer','inverse','bits','published','output','windows','expressions','nodes'}
    if (set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=
        ('shieldd-transfer-epk-fixed-v1','transfer',SCOPE) or
        obj['lane'] not in ('recovery','encryption') or (not source_only and obj['lane']!='recovery')):
        raise relation.RelationError('EPK fixed closed recovery schema/scope')
    if not isinstance(accepted_capsules,dict) or not isinstance(accepted_roles,dict):
        raise relation.RelationError('EPK independently typed capsule/caller parents required')
    capsules=accepted_capsules.get('metadata',{});caller=accepted_roles.get('metadata',{})
    if not source_only and (capsules.get('schema')!='shieldd-transfer-recovery-capsule-roles-v1' or
        any(capsules.get(k)!=obj[k] or caller.get(k)!=obj[k] for k in IDENTITY) or
        capsules.get('ordinary_full_ordered_rows_equal') is not True or capsules.get('repeated_observations_equal') is not True or
        not isinstance(accepted_capsules.get('observed'),dict) or not isinstance(accepted_roles.get('observed'),dict)):
        raise relation.RelationError('EPK accepted exact recovery/caller relation identity')
    wanted=False if qualification_parent_sha256 is not None else True
    if obj['ordinary_full_ordered_rows_equal'] is not wanted or obj['repeated_observations_equal'] is not wanted:
        raise relation.RelationError('EPK original qualification flags')
    if obj['relation_digest']!='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236':
        raise relation.RelationError('EPK exact original relation digest')
    domain=relation.natural(obj['domain_size']);copy=relation.natural(obj['constant_copy'],domain)
    if (domain,obj['full_rows'],copy)!=(262144,200770,200692):
        raise relation.RelationError('EPK original Transfer shape')
    slot=relation.natural(obj['slot'],2 if obj['lane']=='recovery' else 4);start=relation.natural(obj['window_start'],126);count=relation.natural(obj['window_count'],17)
    if not 1<=count<=16 or start+count>126 or type(obj['total_windows']) is not int or obj['total_windows']!=126 or type(obj['bit_width']) is not int or obj['bit_width']!=252:
        raise relation.RelationError('EPK exact126/252 window bounds')
    if not source_only:
        entries=capsules.get('capsules');spend=caller.get('spend')
        if not isinstance(entries,list) or len(entries)!=2 or not isinstance(spend,dict):
            raise relation.RelationError('EPK exact native caller/recovery role inventory')
        entry=entries[slot]
        if (obj['randomizer']!=entry.get('randomizer') or obj['bits']!=entry.get('bits') or
            obj['published']!=entry.get('capsule',[])[:2] or obj['output']!=entry.get('computed_epk') or obj['base']!=spend.get('generator') or obj['inverse']!=entry.get('epk_inverse')):
            raise relation.RelationError('EPK same actual scalar/published/computed/standard-generator roles')
    bits=tuple(source_index(bit) for bit in obj['bits'])
    if len(bits)!=252 or len(set(bits))!=252 or any(tag!=1 for tag,_ in bits):
        raise relation.RelationError('EPK distinct252 witness bits')
    roots=set(bits)
    def observed(value):
        if not isinstance(value,dict) or len(value)!=1:raise relation.RelationError('EPK observed value')
        if set(value)=={'native'}:return canonical([(0,fixed._native(value))])
        if set(value)!={'source'}:raise relation.RelationError('EPK unknown observed kind')
        handle=source_index(value['source']);roots.add(handle);return handle
    def refs(values,n):
        if not isinstance(values,list) or len(values)!=n:raise relation.RelationError('EPK array arity')
        return tuple(observed(value) for value in values)
    observed(obj['randomizer']);observed(obj['inverse']);refs(obj['published'],2);refs(obj['output'],2)
    if not isinstance(obj['base'],list) or len(obj['base'])!=2:raise relation.RelationError('EPK native base arity')
    generator=tuple(fixed._native(v) for v in obj['base'])
    if (generator[1]**2-generator[0]**2-1-fixed.D*generator[0]**2*generator[1]**2)%relation.MODULUS:
        raise relation.RelationError('EPK standard base off curve')
    windows=obj['windows']
    if not isinstance(windows,list) or len(windows)!=count:raise relation.RelationError('EPK incomplete bounded windows')
    for offset,w in enumerate(windows):
        if (not isinstance(w,dict) or set(w)!={'index','table','points','bits','arithmetic','quotient'} or
            type(w['index'])is not int or w['index']!=start+offset or not isinstance(w['table'],list) or len(w['table'])!=4 or
            not isinstance(w['points'],list) or len(w['points'])!=3 or
            tuple(source_index(bit) for bit in w['bits'])!=bits[2*(start+offset):2*(start+offset)+2]):
            raise relation.RelationError('EPK closed indexed window/ascending bit order')
        for point in w['points']:refs(point,2)
        refs(w['arithmetic'],4);refs(w['quotient'],6)
    expressions,nodes,derived,boundaries=_source_cone(obj,roots,domain,copy)
    def value(ref):
        if 'native' in ref:return canonical([(0,fixed._native(ref))])
        return derived[source_index(ref['source'])]
    def values(refs):return tuple(value(ref) for ref in refs)
    output=values(obj['output']);points=[];tables=[];products=[];quotients=[]
    weighted=generator
    for _ in range(start):weighted=fixed._add(fixed._add(weighted,weighted),fixed._add(weighted,weighted))
    for offset,w in enumerate(windows):
        index=start+offset;table=tuple(tuple(fixed._native(v) for v in p) for p in w['table'])
        if any(len(p)!=2 for p in table):raise relation.RelationError('EPK native table arity')
        base,twice,triple,next_base=table
        if (twice!=fixed._add(base,base) or triple!=fixed._add(twice,base) or next_base!=fixed._add(twice,twice) or
            (offset==0 and base!=weighted) or (tables and tables[-1][3]!=base)):
            raise relation.RelationError('EPK native fixed table2/3/4 recurrence')
        before,selected,after=tuple(values(p) for p in w['points'])
        if points and points[-1][2]!=before:raise relation.RelationError('EPK accumulator LC continuity')
        if index==0 and before!=((),((0,1),)):raise relation.RelationError('EPK initial identity')
        if index==125 and after!=output:raise relation.RelationError('EPK full endpoint role')
        xx,yy,total,xy=values(w['arithmetic']);q=values(w['quotient'])
        dt=canonical((c,v*fixed.D) for c,v in xy)
        if q!=(combine(combine(total,xx,-1),yy,-1),combine(yy,xx),combine(((0,1),),dt),combine(((0,1),),dt,-1),*after):
            raise relation.RelationError('EPK actual quotient formula/operands')
        low,high=(expressions[h] for h in bits[2*index:2*index+2])
        for axis in range(2):
            lo=combine(canonical([(0,axis)]),canonical((c,v*(base[axis]-axis)) for c,v in low))
            hi=combine(canonical([(0,twice[axis])]),canonical((c,v*(triple[axis]-twice[axis])) for c,v in low))
            products.append((f'window.{index}.select.{axis}',high,combine(hi,lo,-1),combine(selected[axis],lo,-1)))
        for name,left,right,result in [('xx',before[0],selected[0],xx),('yy',before[1],selected[1],yy),
            ('sum',combine(*before),combine(*selected),total),('xy',xx,yy,xy)]:products.append((f'window.{index}.{name}',left,right,result))
        quotients.extend((f'window.{index}.quotient.{axis}',q[axis],q[axis+2],q[axis+4]) for axis in range(2))
        points.append((before,selected,after));tables.append(table)
    for _,left,right,result in products:
        for scalar,other in ((left,right),(right,left)):
            if not scalar or all(c==0 for c,_ in scalar):
                factor=scalar[0][1] if scalar else 0
                if result!=canonical((c,v*factor) for c,v in other):raise relation.RelationError('EPK folded product LC mismatch')
                break
    for owner in (() if source_only else (accepted_capsules,accepted_roles)):
        for handle in set(expressions)&set(owner['observed']):
            if expressions[handle]!=owner['observed'][handle]:raise relation.RelationError('EPK shared parent LC mismatch')
    return dict(metadata=obj,metadata_sha256=hashlib.sha256(data).hexdigest(),qualification_parent_sha256=qualification_parent_sha256,
        recovery_parent_metadata_sha256=accepted_capsules.get('metadata_sha256'),caller_parent_metadata_sha256=accepted_roles.get('metadata_sha256'),
        expressions=expressions,observed=expressions,nodes=nodes,derived=derived,boundaries=boundaries,products=products,quotients=quotients,
        points=points,tables=tables,scope='typed fixed EPK source/LC/table obligations; original rows/scalar constructor/standard order/native ABI/point semantics OPEN')

def _source_cone(obj,roots,domain,copy):
    if not isinstance(obj['expressions'],list) or not 1<=len(obj['expressions'])<=4096:
        raise relation.RelationError('EPK fixed LC4096 bound')
    expressions={};previous=(-1,-1);term_count=0
    for item in obj['expressions']:
        if not isinstance(item,dict) or set(item)!={'source','terms'}:raise relation.RelationError('EPK fixed LC shape')
        source=source_index(item['source']);relation.terms(item['terms'],domain)
        if source<=previous:raise relation.RelationError('EPK fixed LC order')
        previous=source;term_count+=len(item['terms'])
        if term_count>65536:raise relation.RelationError('EPK fixed LC total term bound')
        terms=tuple((column,int(value,16)) for column,value in item['terms'])
        if any(column==copy for column,_ in terms) or (source[0]==0 and any(column!=0 for column,_ in terms)):
            raise relation.RelationError('EPK fixed pre-outline constant LC')
        if source[0]==1 and terms!=((source[1]+3,1),):raise relation.RelationError('EPK fixed witness LC identity')
        expressions[source]=terms
    if not roots<=set(expressions):raise relation.RelationError('EPK fixed missing role LC')
    if not isinstance(obj['nodes'],list) or len(obj['nodes'])>8192:raise relation.RelationError('EPK fixed node8192 bound')
    nodes={};previous=-1
    for item in obj['nodes']:
        if not isinstance(item,dict) or set(item)!={'index','multiply','left','right'}:raise relation.RelationError('EPK fixed node shape')
        index=relation.natural(item['index'],2**32);left,right=source_index(item['left']),source_index(item['right'])
        if index<=previous or type(item['multiply'])is not bool or any(tag==2 and child>=index for tag,child in (left,right)):
            raise relation.RelationError('EPK fixed source topology')
        previous=index;nodes[(2,index)]=(item['multiply'],left,right)
    boundaries={source_index(value['source']) for value in obj['windows'][0]['points'][0] if 'source' in value}
    if obj['window_start']+obj['window_count']<126:
        boundaries.update(source_index(value['source']) for value in obj['output'] if 'source' in value)
    pending=list(roots);visited=set();required=set(roots)
    while pending:
        source=pending.pop()
        if source in visited:continue
        visited.add(source)
        if len(visited)>8192:raise relation.RelationError('EPK fixed source cone bound')
        if source[0]==2:
            if source not in nodes:raise relation.RelationError('EPK fixed missing source node')
            multiply,left,right=nodes[source]
            if source in boundaries:continue
            if multiply and left[0]!=0 and right[0]!=0:required.update((source,left,right))
            pending.extend((left,right))
        else:required.add(source)
    if set(nodes)!={source for source in visited if source[0]==2} or set(expressions)!=required:
        raise relation.RelationError('EPK fixed missing/extra source graph or LC')
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
        if source in expressions and value!=expressions[source]:raise relation.RelationError('EPK fixed source affine LC mismatch')
        derived[source]=value
    return expressions,nodes,derived,boundaries



def inspect_recovery_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles):
    """Typed derivative of an actual eight-page qualifier, preserving FALSE raw flags."""
    import blake3
    if not isinstance(qualified_parent,bytes) or not 0<len(qualified_parent)<=32768:
        raise relation.RelationError('EPK fixed parent32768 bound')
    parent=relation.record(qualified_parent)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','lane','slot','pages'}
    if (set(parent)!=keys or (parent['schema'],parent['family'],parent['scope'],parent['lane'])!=
        ('shieldd-transfer-epk-fixed-pages-v1','transfer',PARENT_SCOPE,'recovery') or
        parent['ordinary_full_ordered_rows_equal'] is not True or parent['repeated_observations_equal'] is not True or
        not isinstance(parent['pages'],list) or len(parent['pages'])!=8 or not isinstance(raw_pages,list) or len(raw_pages)!=8):
        raise relation.RelationError('EPK fixed qualified exacteight recovery pages parent')
    parent_digest=hashlib.sha256(qualified_parent).hexdigest();chunks=[];observed={};previous=None
    for ordinal,(descriptor,data) in enumerate(zip(parent['pages'],raw_pages)):
        start,count=16*ordinal,min(16,126-16*ordinal)
        if (not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','window_start','window_count','blake3'} or
            any(type(descriptor[key])is not int or descriptor[key]!=value for key,value in
                (('ordinal',ordinal),('window_start',start),('window_count',count))) or
            not isinstance(data,bytes) or not 0<len(data)<=2*1024*1024 or
            descriptor['blake3']!=blake3.blake3(data).hexdigest()):
            raise relation.RelationError('EPK fixed page descriptor/order/byte identity')
        checked=_inspect_recovery_page(data,accepted_capsules,accepted_roles,parent_digest);obj=checked['metadata']
        if obj['window_start']!=start or obj['window_count']!=count or any(obj[key]!=parent[key] for key in (*IDENTITY,'lane','slot')):
            raise relation.RelationError('EPK fixed raw page/qualified parent identity')
        if previous is not None:
            if previous['points'][-1][2]!=checked['points'][0][0] or previous['tables'][-1][3]!=checked['tables'][0][0]:
                raise relation.RelationError('EPK fixed crosspage accumulator/table chain')
            common=('base','randomizer','inverse','bits','published','output')
            if any(previous['metadata'][key]!=obj[key] for key in common):
                raise relation.RelationError('EPK fixed crosspage shared source roles')
        for handle,terms in checked['expressions'].items():
            if handle in observed and observed[handle]!=terms:raise relation.RelationError('EPK fixed crosspage LC disagreement')
            observed[handle]=terms
        chunks.append(checked);previous=checked
    return dict(parent=parent,parent_sha256=parent_digest,chunks=chunks,observed=observed,
        raw_page_sha256=[hashlib.sha256(data).hexdigest() for data in raw_pages],
        scope='Derivative full126 fixed EPK source/LC coverage retaining FALSE raw flags; original row replay/scalar and native constructor proofs OPEN')


def inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles):
    """Six scoped source views of one actual qualifier; raw FALSE flags remain intact.

    Recovery slots additionally join independently typed74 roles. Encryption source
    scopes join the common generator/caller LCs; broad native encryption-slot object
    association is an explicit remaining obligation, not invented typed metadata.
    """
    import blake3
    if not isinstance(qualified_parent,bytes) or not 0<len(qualified_parent)<=32768:
        raise relation.RelationError('EPK all parent32768 bound')
    parent=relation.record(qualified_parent)
    keys={'schema','family','scope',*IDENTITY,'ordinary_full_ordered_rows_equal','repeated_observations_equal','scopes','pages'}
    if (set(parent)!=keys or (parent['schema'],parent['family'],parent['scope'])!=
        ('shieldd-transfer-epk-all-fixed-pages-v1','transfer',ALL_PARENT_SCOPE) or
        parent['ordinary_full_ordered_rows_equal'] is not True or parent['repeated_observations_equal'] is not True or
        not isinstance(parent['scopes'],list) or len(parent['scopes'])!=6 or
        not isinstance(parent['pages'],list) or len(parent['pages'])!=48 or
        not isinstance(raw_pages,list) or len(raw_pages)!=48):
        raise relation.RelationError('EPK all qualified exact6/48 parent')
    caller=_qualified_caller_identity(accepted_roles,parent)
    parent_sha=hashlib.sha256(qualified_parent).hexdigest();groups=[];observed={};nodes={};private=set()
    for scope_id in range(6):
        lane,slot=('recovery',scope_id) if scope_id<2 else ('encryption',scope_id-2)
        scope=parent['scopes'][scope_id]
        if (not isinstance(scope,dict) or set(scope)!={'lane','slot','randomizer','published','output','inverse'} or
            scope['lane']!=lane or type(scope['slot'])is not int or scope['slot']!=slot):
            raise relation.RelationError('EPK all source scope order')
        chunks=[];previous=None
        for local in range(8):
            ordinal=8*scope_id+local;start,count=16*local,min(16,126-16*local)
            descriptor=parent['pages'][ordinal];data=raw_pages[ordinal]
            if (not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','scope_id','window_start','window_count','blake3'} or
                any(type(descriptor[k])is not int or descriptor[k]!=v for k,v in
                    (('ordinal',ordinal),('scope_id',scope_id),('window_start',start),('window_count',count))) or
                not isinstance(data,bytes) or not 0<len(data)<=2*1024*1024 or descriptor['blake3']!=blake3.blake3(data).hexdigest()):
                raise relation.RelationError('EPK all descriptor/order/byte identity')
            checked=(_inspect_recovery_page(data,accepted_capsules,accepted_roles,parent_sha) if lane=='recovery' else
                _inspect_page_source(data,{},accepted_roles,parent_sha,source_only=True))
            obj=checked['metadata']
            if (any(obj[k]!=parent[k] for k in IDENTITY) or any(obj[k]!=scope[k] for k in scope) or
                obj['window_start']!=start or obj['window_count']!=count or obj['base']!=caller['spend'].get('generator')):
                raise relation.RelationError('EPK all exact source scalar/endpoints/common generator')
            if local==0:
                handles=[source_index(obj[key].get('source')) for key in ('randomizer','inverse')]+list(map(source_index,obj['bits']))
                if any(h[0]!=1 for h in handles) or len(set(handles))!=254 or private.intersection(handles):
                    raise relation.RelationError('EPK all private scalar/bits/inverse alias')
                private.update(handles)
            if previous is not None:
                if (any(previous['metadata'][k]!=obj[k] for k in ('base','randomizer','inverse','bits','published','output','lane','slot')) or
                    previous['points'][-1][2]!=checked['points'][0][0] or previous['tables'][-1][3]!=checked['tables'][0][0]):
                    raise relation.RelationError('EPK all complete6x126 continuity')
            for handle,terms in checked['expressions'].items():
                if ((handle in observed and observed[handle]!=terms) or
                    (handle in accepted_roles['observed'] and accepted_roles['observed'][handle]!=terms)):
                    raise relation.RelationError('EPK all common source LC disagreement')
                observed[handle]=terms
            for handle,node in checked['nodes'].items():
                if handle in nodes and nodes[handle]!=node:raise relation.RelationError('EPK all common source AST disagreement')
                nodes[handle]=node
            chunks.append(checked);previous=checked
        groups.append(dict(lane=lane,slot=slot,chunks=chunks))
    return dict(parent=parent,parent_sha256=parent_sha,scopes=groups,observed=observed,nodes=nodes,
        raw_page_sha256=[hashlib.sha256(data).hexdigest() for data in raw_pages],
        scope='Derivative six complete126-window source/LC/native table views retaining FALSE raw flags; actual rows/scalar construction/native encryption object association OPEN')
