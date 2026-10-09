"""Exact local balance129 template correspondence after genuine joint ingress.

This is optional source planning, not a certificate or a substitute for a proved
template constructor. Window0 retains its folded/odd-padding constructor. H126
has a distinct native generator and is never accepted by this adapter.
"""
from . import transfer_balance_variable_program as programs
from . import transfer_balance_variable_completion as completion
from . import transfer_relation as relation

MAX_COLUMNS=512
MAX_ROWS=128
_PIVOTS={'output','auxiliary','quotient','product'}
_LCS={'left','right','input','numerator','denominator','remainder'}


class _Columns:
    def __init__(self,protected):
        self.protected=set(protected);self.forward={};self.reverse={}
        for column in self.protected:self.add(column,column)

    def add(self,left,right):
        relation.natural(left,262144);relation.natural(right,262144)
        if (left in self.protected or right in self.protected) and left!=right:
            raise relation.RelationError('balance renaming protected original source column')
        if left in self.forward and self.forward[left]!=right:
            raise relation.RelationError('balance renaming source column conflict')
        if right in self.reverse and self.reverse[right]!=left:
            raise relation.RelationError('balance renaming restricted injection conflict')
        if left not in self.forward and len(self.forward)>=MAX_COLUMNS:
            raise relation.RelationError('balance renaming bounded local support')
        self.forward[left]=right;self.reverse[right]=left

    def roles(self,left,right):
        if len(left)!=len(right):raise relation.RelationError('balance renaming exact role LC arity')
        for (a,x),(b,y) in zip(left,right,strict=True):
            if type(x)is not int or type(y)is not int or x!=y:
                raise relation.RelationError('balance renaming exact role coefficient')
            self.add(a,b)

    def lc(self,terms):
        try:return tuple((self.forward[column],value) for column,value in terms)
        except KeyError as error:raise relation.RelationError('balance renaming unknown stage/source support') from error

    def permutation(self):
        """Close each finite injection chain; cycles and fixed points stay exact.

        Unlike disjoint transpositions this supports adjacent-window overlap.
        Every authored edge is retained and both total lookup functions use
        identity outside the resulting finite common domain/range.
        """
        result=dict(self.forward)
        for start in sorted(set(self.forward)-set(self.reverse)):
            end=start;visited=set()
            while end in self.forward:
                if end in visited:raise relation.RelationError('balance renaming invalid finite chain')
                visited.add(end);end=self.forward[end]
            if end in result:raise relation.RelationError('balance renaming chain endpoint collision')
            result[end]=start
        if set(result)!=set(result.values()) or len(set(result.values()))!=len(result):
            raise relation.RelationError('balance renaming finite permutation closure')
        if len(result)>2*MAX_COLUMNS:raise relation.RelationError('balance renaming bounded permutation')
        inverse={target:source for source,target in result.items()}
        if any(inverse[result[source]]!=source for source in result):
            raise relation.RelationError('balance renaming exact finite inverse')
        return sorted(result.items()),sorted(inverse.items())


def _stages(columns,left,right):
    if len(left)!=len(right):raise relation.RelationError('balance renaming exact stage count')
    for source,target in zip(left,right,strict=True):
        if set(source)!=set(target) or source.get('kind')!=target.get('kind'):
            raise relation.RelationError('balance renaming exact stage schema/order')
        if source['kind'] not in ('square','product','quotient','linear'):
            raise relation.RelationError('balance renaming unsupported stage kind')
        for key in _PIVOTS&set(source):columns.add(source[key],target[key])
        for key in _LCS&set(source):
            if columns.lc(source[key])!=tuple(target[key]):
                raise relation.RelationError('balance renaming exact ordered stage LC/coefficient')
        if len(source['rows'])!=len(target['rows']):
            raise relation.RelationError('balance renaming exact physical row arity')
        for key in set(source)-_PIVOTS-_LCS-{'role','rows'}:
            if source[key]!=target[key]:raise relation.RelationError('balance renaming stage constant drift')


def _pair(accepted,source_index,target_index):
    if (type(source_index)is not int or type(target_index)is not int or
            not 1<=source_index<65 or not 1<=target_index<65):
        raise relation.RelationError('balance renaming excludes folded/odd-padding window0')
    a,b=(accepted['programs'][index] for index in (source_index,target_index))
    if a['index']!=source_index or b['index']!=target_index:
        raise relation.RelationError('balance renaming exact complete program indices')
    pages=accepted['checked']['chunks']
    left,right=(pages[item['page_ordinal']] for item in (a,b))
    if any(page['metadata']['schema']!='shieldd-transfer-balance-variable-v1' or
           page['metadata']['bit_width']!=129 or page['metadata']['total_windows']!=65 for page in (left,right)):
        raise relation.RelationError('balance renaming distinct actual balance129 schema')
    copy=left['metadata']['constant_copy']
    if copy!=right['metadata']['constant_copy'] or copy!=200692:
        raise relation.RelationError('balance renaming original constant copy')
    columns=_Columns({0,1,2,6,9,22737,copy})
    def observed(page,value):
        return page['derived'][value[1]] if value[0]=='source' else completion.canonical([(0,value[1])])
    for role in ('base','twice','triple'):
        if left['points'][role]!=right['points'][role]:
            raise relation.RelationError('balance renaming SAME actual native asset table source roles')
        for lv,rv in zip(left['points'][role],right['points'][role],strict=True):
            columns.roles(observed(left,lv),observed(right,rv))
    for lv,rv in zip(a['incoming'],b['incoming'],strict=True):
        columns.roles(observed(left,lv),observed(right,rv))
    for lv,rv in zip(a['bits'],b['bits'],strict=True):
        columns.roles(observed(left,lv),observed(right,rv))
    pa,pb=a['plan'],b['plan']
    group_shape=lambda plan:[(item['stage_start'],item['material_end'],item['stage_end'],item['kind']) for item in plan['point_groups']]
    if group_shape(pa)!=group_shape(pb):raise relation.RelationError('balance renaming exact two-double/add groups')
    _stages(columns,pa['stages'],pb['stages'])
    for lv,rv in zip(a['outgoing'],b['outgoing'],strict=True):
        if columns.lc(observed(left,lv))!=observed(right,rv):
            raise relation.RelationError('balance renaming exact output source LC')
    if sorted(columns.forward[c] for c in a['writes'])!=b['writes']:
        raise relation.RelationError('balance renaming exact owned writes')
    rows_a=programs._rows(accepted['selections'][a['page_ordinal']],a['rows'])
    rows_b=programs._rows(accepted['selections'][b['page_ordinal']],b['rows'])
    if len(rows_a)!=len(rows_b) or not 1<=len(rows_a)<=MAX_ROWS:
        raise relation.RelationError('balance renaming exact bounded original rows')
    target={row:index for index,row in rows_b.items()}
    if len(target)!=len(rows_b):raise relation.RelationError('balance renaming unique original target shapes')
    matched=[]
    for index,row in sorted(rows_a.items()):
        renamed=tuple(columns.lc(side) for side in row)
        if renamed not in target:raise relation.RelationError('balance renaming exact original row coefficients/order')
        matched.append((index,target[renamed]))
    if len({index for _,index in matched})!=len(rows_b):
        raise relation.RelationError('balance renaming full target original-row coverage')
    # Accepted program.plan already proves all writes avoid original shared,
    # signed and prior rows. Recheck target ownership here for this reuse path.
    if set(b['writes'])&set(accepted['protected']):
        raise relation.RelationError('balance renaming destroys actual protected frame')
    forward,inverse=columns.permutation()
    return dict(source_window=source_index,target_window=target_index,columns=forward,inverse=inverse,
        row_pairs=matched,writes=b['writes'],protected=accepted['protected'],
        before_frame=b['before_frame'],after_frame=b['after_frame'],
        parent_sha256=accepted['parent_sha256'],raw_page_sha256=accepted['raw_page_sha256'],identity=accepted['identity'],
        qualification=False,scope='Exact local source/LC/stage/original-row permutation only. Source template constructor/formula, global permutation proof, actual native table association and whole-loop outside frame still require kernel instantiation. Full per-window fallback preserved; no H reuse.')


def from_ingress(parent,pages,digest,signed,asset_base,extracted,readonly_lcs=(),*,compiler_origin=22738):
    accepted=programs.plan(parent,pages,digest,signed,asset_base,extracted,readonly_lcs,compiler_origin=compiler_origin)
    matches=[];fallback=[]
    for target in range(2,65):
        try:matches.append(_pair(accepted,1,target))
        except relation.RelationError as error:fallback.append(dict(window=target,reason=str(error)))
    return dict(template_window=1,separate_folded_window=0,matches=matches,fallback=fallback,
        parent_sha256=accepted['parent_sha256'],raw_page_sha256=accepted['raw_page_sha256'],
        qualification=False,certification=False,ordinary_replays=0,
        scope='Optional exact balance129 local template plans only; kernel constructors and same-value native/frame joins mandatory. No replay or target qualification inferred.')
