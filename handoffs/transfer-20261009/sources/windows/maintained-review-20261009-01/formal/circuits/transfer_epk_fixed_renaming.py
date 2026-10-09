"""Optional exact six-EPK correspondence, after genuine ingress/one row replay.

This does not generate proofs or declare kernel equivalence. Unsupported shapes
refuse; the full per-scope renderer remains available. VALUE_BLINDING is absent.
"""
from . import transfer_epk_fixed_sequence as sequence,transfer_relation as relation

MAX_COLUMNS=8192
MAX_ROWS=16384
LC_KEYS={'left','right','input','numerator','denominator','remainder'}
COLUMN_KEYS={'output','auxiliary','quotient','product'}


class _Map:
    """Restricted injection, extended by disjoint support transpositions only."""
    def __init__(self,protected):
        self.forward={};self.reverse={};self.protected=set(protected)
        for column in self.protected:self.add(column,column)

    def add(self,source,target):
        relation.natural(source,262144);relation.natural(target,262144)
        if (source in self.protected or target in self.protected) and source!=target:
            raise relation.RelationError('EPK renaming protected source/public/committed/copy column')
        if source in self.forward and self.forward[source]!=target:
            raise relation.RelationError('EPK renaming conflicting source column')
        if target in self.reverse and self.reverse[target]!=source:
            raise relation.RelationError('EPK renaming restricted injection conflict')
        if len(self.forward)>=MAX_COLUMNS and source not in self.forward:
            raise relation.RelationError('EPK renaming bounded column support')
        self.forward[source]=target;self.reverse[target]=source

    def lc(self,terms):
        if len(terms)>4096:raise relation.RelationError('EPK renaming bounded actual LC terms')
        result=[]
        for column,coefficient in terms:
            if column not in self.forward:
                raise relation.RelationError('EPK renaming unmapped actual source LC column')
            if type(coefficient)is not int:
                raise relation.RelationError('EPK renaming exact integer coefficient required')
            result.append((self.forward[column],coefficient))
        # Preserve exact ordering/coefficients. No canonicalization, sign
        # reflection, modular scaling or solver identity is presumed here.
        return tuple(result)

    def permutation(self):
        moving={source:target for source,target in self.forward.items() if source!=target}
        if set(moving)&set(moving.values()):
            raise relation.RelationError('EPK renaming non-disjoint cone supports need full fallback')
        permutation={**moving,**{target:source for source,target in moving.items()}}
        if len(permutation)!=2*len(moving):
            raise relation.RelationError('EPK renaming finite permutation collision')
        return sorted(permutation.items())


def _stage(columns,left,right):
    if set(left)!=set(right) or left.get('kind')!=right.get('kind'):
        raise relation.RelationError('EPK renaming exact lowered stage schema/kind/order')
    if left['kind'] not in ('product','quotient','linear'):
        raise relation.RelationError('EPK renaming unsupported lowered stage')
    for key in COLUMN_KEYS&set(left):columns.add(left[key],right[key])
    for key in left:
        if key in COLUMN_KEYS:continue
        if key in LC_KEYS:
            if columns.lc(left[key])!=tuple(right[key]):
                raise relation.RelationError('EPK renaming exact stage source LC/coefficient')
        elif key=='rows':
            if len(left[key])!=len(right[key]):
                raise relation.RelationError('EPK renaming exact stage physical row arity')
        elif left[key]!=right[key]:
            raise relation.RelationError('EPK renaming exact stage role/constant')


def _rows(columns,original,target):
    if len(original)!=len(target) or len(original)>MAX_ROWS:
        raise relation.RelationError('EPK renaming bounded exact original row count')
    by_shape={}
    for index,row in target.items():by_shape.setdefault(tuple(map(tuple,row)),[]).append(index)
    matching=[];used=set()
    for index,row in sorted(original.items()):
        renamed=tuple(columns.lc(side) for side in row)
        found=by_shape.get(renamed,[])
        if len(found)!=1 or found[0] in used:
            raise relation.RelationError('EPK renaming unique exact original row correspondence')
        used.add(found[0]);matching.append((index,found[0]))
    if used!=set(target):raise relation.RelationError('EPK renaming full original row coverage')
    return matching


def _pair(accepted,target_id):
    source=accepted['locals'][0];target=accepted['locals'][target_id]
    shared={0,1,2,6,source['checked']['parent']['constant_copy']}
    if target['checked']['parent']['constant_copy'] not in shared:
        raise relation.RelationError('EPK renaming exact shared constant copy')
    columns=_Map(shared)
    if (source['identity']!=target['identity'] or
            source['parent_sha256']!=target['parent_sha256'] or
            source['raw_page_sha256']!=target['raw_page_sha256']):
        raise relation.RelationError('EPK renaming same genuine full parent/page/row identity')
    if source['chunks'][0]['metadata']['base']!=target['chunks'][0]['metadata']['base']:
        raise relation.RelationError('EPK renaming exact SP native generator/table association')
    for left,right in zip(source['chunks'],target['chunks']):
        if left['metadata']['window_start']!=right['metadata']['window_start'] or left['tables']!=right['tables']:
            raise relation.RelationError('EPK renaming complete native table/window correspondence')
    columns.add(source['scalar']['value'],target['scalar']['value'])
    for offset in range(252):columns.add(source['scalar']['bit_start']+offset,target['scalar']['bit_start']+offset)
    for left,right in zip(source['boundary']['published'],target['boundary']['published']):
        if len(left)!=1 or len(right)!=1 or left[0][1]!=1 or right[0][1]!=1:
            raise relation.RelationError('EPK renaming native published source singleton roles')
        columns.add(left[0][0],right[0][0])
    stages_left=source['scalar']['stages'];stages_right=target['scalar']['stages']
    if len(stages_left)!=len(stages_right):raise relation.RelationError('EPK renaming exact comparator stage count')
    for left,right in zip(stages_left,stages_right):_stage(columns,left,right)
    windows_left=source['loop']['programs'];windows_right=target['loop']['programs']
    if len(windows_left)!=126 or len(windows_right)!=126:
        raise relation.RelationError('EPK renaming complete fixed126 required')
    for index,(left,right) in enumerate(zip(windows_left,windows_right)):
        if left['index']!=index or right['index']!=index or len(left['stages'])!=len(right['stages']):
            raise relation.RelationError('EPK renaming exact fixed window/stage order')
        for old,new in zip(left['stages'],right['stages']):_stage(columns,old,new)
        for role in ('input','output'):
            if tuple(columns.lc(lc) for lc in left[role])!=tuple(right[role]):
                raise relation.RelationError('EPK renaming exact fixed source endpoint adjacency')
        if left['folded_products']!=right['folded_products'] or left['folded_quotients']!=right['folded_quotients']:
            raise relation.RelationError('EPK renaming exact folded operation role/order')
    # Check the source operands even for folded operations which emitted no
    # stage/row. A matching folded role name alone proves no correspondence.
    for left,right in zip(source['chunks'],target['chunks']):
        for key in ('products','quotients'):
            if len(left[key])!=len(right[key]):raise relation.RelationError('EPK renaming exact source arithmetic arity')
            for old,new in zip(left[key],right[key]):
                if old[0]!=new[0] or len(old)!=len(new):raise relation.RelationError('EPK renaming exact source arithmetic role/order')
                if any(columns.lc(a)!=tuple(b) for a,b in zip(old[1:],new[1:])):
                    raise relation.RelationError('EPK renaming complete source arithmetic operands')
    _stage(columns,dict(kind='quotient',**source['boundary']['inverse_constructor']),
        dict(kind='quotient',**target['boundary']['inverse_constructor']))
    for role in ('published','computed'):
        if tuple(columns.lc(lc) for lc in source['boundary'][role])!=tuple(target['boundary'][role]):
            raise relation.RelationError('EPK renaming exact native boundary LC association')
    original=sequence._rows(source);actual=sequence._rows(target)
    row_map=_rows(columns,original,actual)
    source_writes=set(sequence._writes(source));target_writes=set(sequence._writes(target))
    if {columns.forward[column] for column in source_writes}!=target_writes:
        raise relation.RelationError('EPK renaming exact owned writes/frame correspondence')
    return dict(scope_id=target_id,restricted_map=sorted(columns.forward.items()),
        permutation=columns.permutation(),original_row_map=row_map,source_writes=sorted(source_writes),
        target_writes=sorted(target_writes),source_frame=accepted['steps'][0]['fence'],target_frame=accepted['steps'][target_id]['fence'],
        scalar_source_roles=[source['loop']['scalar_source'],target['loop']['scalar_source']],
        published_source_roles=[source['loop']['published_sources'],target['loop']['published_sources']],
        inverse_source_roles=[source['loop']['inverse_source'],target['loop']['inverse_source']])


def plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted):
    """No extra stream: strict genuine48 + persisted row union before matching."""
    accepted=sequence.plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted)
    pairs=[_pair(accepted,index) for index in range(1,6)]
    return dict(source_scope=0,targets=pairs,identity=accepted['identity'],parent_sha256=accepted['parent_sha256'],
        raw_page_sha256=accepted['raw_page_sha256'],protected_public_committed_copy=[0,1,2,200692],
        ordinary_replays=0,qualification=False,certification=False,
        scope='Exact bounded source/LC/stage/original-row correspondence only; checked renaming kernel and native/frame proof transport still required; full per-scope fallback retained')
