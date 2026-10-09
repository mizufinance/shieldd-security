"""Genuine VALUE_BLINDING fixed252 ingress, including canonical scalar zero.

No spend/EPK packet is converted to this schema. The shared source-cone routine
checks exact compiler AST/LC correspondence; independent native parameter and
caller scalar association must be supplied explicitly, never by a hash alone.
"""
import hashlib
from . import transfer_relation as relation,transfer_fixed_spend as fixed
from .transfer_epk_fixed import _source_cone
from .transfer_balance_rows import canonical,combine,source_index

SCOPE='bounded VALUE_BLINDING fixed source roles; row/native claims open'
PARENT_SCOPE='8 bounded VALUE_BLINDING fixed pages from one lowering; row/native claims open'
DIGEST='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'
IDENTITY=('relation_digest','domain_size','full_rows','constant_copy')


def _identity(obj):
    if (obj.get('relation_digest')!=DIGEST or any(type(obj.get(k))is not int or obj[k]!=v for k,v in
        (('domain_size',262144),('full_rows',200770),('constant_copy',200692)))):
        raise relation.RelationError('balance blinding exact production relation/shape')


def inspect_page(data,expected_base,expected_blinding,*,qualification_parent_sha256=None):
    if not isinstance(data,bytes) or not 0<len(data)<=2*1024*1024:
        raise relation.RelationError('balance blinding2MiB page bound')
    obj=relation.record(data)
    keys={'schema','family','scope',*IDENTITY,'ordinary_full_ordered_rows_equal','repeated_observations_equal',
        'generator','window_start','window_count','total_windows','bit_width','base','blinding','bits','output','windows','expressions','nodes'}
    if (set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'],obj['generator'])!=
        ('shieldd-transfer-balance-blinding-fixed-v1','transfer',SCOPE,'VALUE_BLINDING')):
        raise relation.RelationError('balance blinding distinct closed schema/scope')
    _identity(obj)
    wanted=qualification_parent_sha256 is None
    if obj['ordinary_full_ordered_rows_equal'] is not wanted or obj['repeated_observations_equal'] is not wanted:
        raise relation.RelationError('balance blinding real qualification flags')
    start=relation.natural(obj['window_start'],126);count=relation.natural(obj['window_count'],17)
    if (not 1<=count<=16 or start+count>126 or type(obj['total_windows'])is not int or obj['total_windows']!=126 or
        type(obj['bit_width'])is not int or obj['bit_width']!=252):
        raise relation.RelationError('balance blinding exact126/252 bounded page')
    if (not isinstance(expected_base,list) or len(expected_base)!=2 or obj['base']!=expected_base or
        obj['blinding']!=expected_blinding or not isinstance(expected_blinding,dict) or set(expected_blinding)!={'source'} or
        source_index(expected_blinding['source'])[0]!=1):
        raise relation.RelationError('balance blinding exact native parameter/caller scalar roles')
    generator=tuple(fixed._native(v) for v in obj['base'])
    if (generator[1]**2-generator[0]**2-1-fixed.D*generator[0]**2*generator[1]**2)%relation.MODULUS:
        raise relation.RelationError('balance blinding native generator off curve')
    if not isinstance(obj['bits'],list):raise relation.RelationError('balance blinding bit array')
    bits=tuple(source_index(bit) for bit in obj['bits'])
    if len(bits)!=252 or len(set(bits))!=252 or any(tag!=1 for tag,_ in bits):
        raise relation.RelationError('balance blinding distinct252 witness bits')
    roots=set(bits)
    def observed(ref):
        if not isinstance(ref,dict) or len(ref)!=1:raise relation.RelationError('balance blinding observed shape')
        if set(ref)=={'native'}:fixed._native(ref);return
        if set(ref)!={'source'}:raise relation.RelationError('balance blinding unknown observed kind')
        roots.add(source_index(ref['source']))
    def refs(values,arity):
        if not isinstance(values,list) or len(values)!=arity:raise relation.RelationError('balance blinding observed array')
        for ref in values:observed(ref)
    observed(obj['blinding']);refs(obj['output'],2)
    windows=obj['windows']
    if not isinstance(windows,list) or len(windows)!=count:raise relation.RelationError('balance blinding incomplete windows')
    for offset,w in enumerate(windows):
        if (not isinstance(w,dict) or set(w)!={'index','table','points','bits','arithmetic','quotient'} or
            type(w['index'])is not int or w['index']!=start+offset or not isinstance(w['table'],list) or len(w['table'])!=4 or
            not isinstance(w['points'],list) or len(w['points'])!=3 or not isinstance(w['bits'],list) or
            tuple(source_index(b) for b in w['bits'])!=bits[2*(start+offset):2*(start+offset)+2]):
            raise relation.RelationError('balance blinding closed ordered window/bit pairing')
        for point in w['points']:refs(point,2)
        for point in w['table']:
            if not isinstance(point,list) or len(point)!=2:raise relation.RelationError('balance blinding native table arity')
            for ref in point:fixed._native(ref)
        refs(w['arithmetic'],4);refs(w['quotient'],6)
    expressions,nodes,derived,boundaries=_source_cone(obj,roots,262144,200692)
    def value(ref):return canonical([(0,fixed._native(ref))]) if 'native' in ref else derived[source_index(ref['source'])]
    def values(refs):return tuple(value(ref) for ref in refs)
    output=values(obj['output']);points=[];tables=[];products=[];quotients=[];weighted=generator
    for _ in range(start):
        twice=fixed._add(weighted,weighted);weighted=fixed._add(twice,twice)
    for offset,w in enumerate(windows):
        index=start+offset;table=tuple(tuple(fixed._native(v) for v in p) for p in w['table']);base,twice,triple,next_base=table
        if (twice!=fixed._add(base,base) or triple!=fixed._add(twice,base) or next_base!=fixed._add(twice,twice) or
            (offset==0 and base!=weighted) or (tables and tables[-1][3]!=base)):
            raise relation.RelationError('balance blinding actual native2/3/4 table recurrence')
        before,selected,after=tuple(values(p) for p in w['points'])
        if points and points[-1][2]!=before:raise relation.RelationError('balance blinding accumulator LC continuity')
        if index==0 and before!=((),((0,1),)):raise relation.RelationError('balance blinding initial identity')
        if index==125 and after!=output:raise relation.RelationError('balance blinding final computed role')
        xx,yy,total,xy=values(w['arithmetic']);q=values(w['quotient']);dt=canonical((c,v*fixed.D) for c,v in xy)
        if q!=(combine(combine(total,xx,-1),yy,-1),combine(yy,xx),combine(((0,1),),dt),combine(((0,1),),dt,-1),*after):
            raise relation.RelationError('balance blinding exact quotient numerator/denominator/output')
        low,high=(expressions[h] for h in bits[2*index:2*index+2])
        for axis in range(2):
            lo=combine(canonical([(0,axis)]),canonical((c,v*(base[axis]-axis)) for c,v in low))
            hi=combine(canonical([(0,twice[axis])]),canonical((c,v*(triple[axis]-twice[axis])) for c,v in low))
            products.append((f'window.{index}.select.{axis}',high,combine(hi,lo,-1),combine(selected[axis],lo,-1)))
        for name,left,right,result in [('xx',before[0],selected[0],xx),('yy',before[1],selected[1],yy),
            ('sum',combine(*before),combine(*selected),total),('xy',xx,yy,xy)]:
            products.append((f'window.{index}.{name}',left,right,result))
        quotients.extend((f'window.{index}.quotient.{axis}',q[axis],q[axis+2],q[axis+4]) for axis in range(2))
        points.append((before,selected,after));tables.append(table)
    for _,left,right,result in products:
        for scalar,other in ((left,right),(right,left)):
            if not scalar or all(c==0 for c,_ in scalar):
                factor=scalar[0][1] if scalar else 0
                if result!=canonical((c,v*factor) for c,v in other):raise relation.RelationError('balance blinding folded product correspondence')
                break
    return dict(metadata=obj,metadata_sha256=hashlib.sha256(data).hexdigest(),qualification_parent_sha256=qualification_parent_sha256,
        expressions=expressions,observed=expressions,nodes=nodes,derived=derived,boundaries=boundaries,
        products=products,quotients=quotients,points=points,tables=tables,
        scope='VALUE_BLINDING source/LC/table only; canonical scalar0 allowed; rows/native parameter association/whole balance OPEN')


def inspect_pages(qualified_parent,raw_pages,expected_base,expected_blinding):
    import blake3
    if not isinstance(qualified_parent,bytes) or not 0<len(qualified_parent)<=32768:
        raise relation.RelationError('balance blinding parent32768 bound')
    parent=relation.record(qualified_parent)
    keys={'schema','family','scope',*IDENTITY,'ordinary_full_ordered_rows_equal','repeated_observations_equal','generator','pages'}
    if (set(parent)!=keys or (parent['schema'],parent['family'],parent['scope'],parent['generator'])!=
        ('shieldd-transfer-balance-blinding-fixed-pages-v1','transfer',PARENT_SCOPE,'VALUE_BLINDING') or
        parent['ordinary_full_ordered_rows_equal'] is not True or parent['repeated_observations_equal'] is not True or
        not isinstance(parent['pages'],list) or len(parent['pages'])!=8 or not isinstance(raw_pages,list) or len(raw_pages)!=8):
        raise relation.RelationError('balance blinding real qualified8-page parent')
    _identity(parent);sha=hashlib.sha256(qualified_parent).hexdigest();chunks=[];observed={};previous=None
    for ordinal,(descriptor,data) in enumerate(zip(parent['pages'],raw_pages)):
        start,count=16*ordinal,min(16,126-16*ordinal)
        if (not isinstance(descriptor,dict) or set(descriptor)!={'ordinal','window_start','window_count','blake3'} or
            any(type(descriptor[k])is not int or descriptor[k]!=v for k,v in (('ordinal',ordinal),('window_start',start),('window_count',count))) or
            not isinstance(data,bytes) or not 0<len(data)<=2*1024*1024 or descriptor['blake3']!=blake3.blake3(data).hexdigest()):
            raise relation.RelationError('balance blinding descriptor/order/exact raw bytes')
        checked=inspect_page(data,expected_base,expected_blinding,qualification_parent_sha256=sha);obj=checked['metadata']
        if (obj['window_start'],obj['window_count'])!=(start,count) or any(obj[k]!=parent[k] for k in IDENTITY):
            raise relation.RelationError('balance blinding raw/parent identity')
        if previous and (previous['points'][-1][2]!=checked['points'][0][0] or previous['tables'][-1][3]!=checked['tables'][0][0] or
            any(previous['metadata'][k]!=obj[k] for k in ('base','blinding','bits','output'))):
            raise relation.RelationError('balance blinding crosspage shared roles/continuity')
        for handle,terms in checked['expressions'].items():
            if handle in observed and observed[handle]!=terms:raise relation.RelationError('balance blinding crosspage LC disagreement')
            observed[handle]=terms
        chunks.append(checked);previous=checked
    return dict(parent=parent,parent_sha256=sha,chunks=chunks,observed=observed,
        raw_page_sha256=[hashlib.sha256(data).hexdigest() for data in raw_pages],
        scope='Derivative genuine8-page blinding fixed126, preserving pending FALSE; original rows/canonical/native/full balance OPEN')
