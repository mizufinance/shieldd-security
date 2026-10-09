"""Exact bounded original-row partition for the owned variable-loop join.

The first arithmetic window includes once-only table precomputation. A local
folded constructor supplies its own selector/linear rows; the preceding native
constructor supplies the table rows. Matching this partition supplies neither
row truth nor a kernel receipt. Those remain separately proved constructors.
"""
from . import transfer_relation as relation
from . import transfer_ownership_completion as completion


def row_partition(original, prior, local, *, domain_size, full_rows):
    """Require every bounded original row in an exact earlier/local row part.

Empty parts are allowed. A repeated physical row index must have exactly the
same ordered LC arrays in both parts. No normalization, hash, output value or
desired satisfaction premise substitutes for that equality.
"""
    domain=relation.natural(domain_size)
    count=relation.natural(full_rows)
    if domain<4 or domain & (domain-1) or not 0<count<=domain:
        raise relation.RelationError('ownership constructor partition relation bounds')
    def checked(rows):
        if not isinstance(rows,list) or len(rows)>8192:
            raise relation.RelationError('ownership constructor bounded row part')
        result={};previous=-1
        for row in rows:
            if not isinstance(row,dict) or set(row)!={'row','a','b'}:
                raise relation.RelationError('ownership constructor physical row schema')
            index=relation.natural(row['row'],count)
            if index<=previous:
                raise relation.RelationError('ownership constructor ordered unique physical rows')
            previous=index
            for side in ('a','b'):relation.terms(row[side],domain)
            result[index]=row
        return result
    demanded,earlier,owned=map(checked,(original,prior,local))
    for index in earlier.keys() & owned.keys():
        if earlier[index]!=owned[index]:
            raise relation.RelationError('ownership constructor shared physical row LC mismatch')
    available={**earlier,**owned}
    for index,row in demanded.items():
        if index not in available:
            raise relation.RelationError('ownership original row missing earlier/local constructor')
        if row!=available[index]:
            raise relation.RelationError('ownership original physical row LC mismatch')
    return dict(original_indices=list(demanded),
                prior_indices=[index for index in demanded if index in earlier],
                local_indices=[index for index in demanded if index in owned],
                shared_indices=sorted(demanded.keys() & earlier.keys() & owned.keys()),
                scope='exact bounded row partition only; constructor truth and kernel/source/native joins separate')


def actual_window_partition(checked, extracted, window_offset, readonly_lcs=()):
    """Bind the arithmetic module's selected rows to real local/prior plans.

    First-window precompute rows are selected from the two actual earlier point
    groups. Later windows select no precomputation. Every row retains its exact
    physical LC arrays from the previously replayed ordinary selection.
    """
    local=completion.window_plan(checked,extracted,window_offset,False,readonly_lcs)
    first=local['window_index']==0
    cones=completion.owner.cone_certificates(checked,extracted,window_offset,first)
    quotients=completion.owner.quotient_certificates(checked,extracted,window_offset,first)
    originals=set(cones['rows']) | set(quotients['rows'])
    earlier=set()
    if first:
        full=completion.window_plan(checked,extracted,window_offset,True,readonly_lcs)
        groups=full['point_groups']
        if len(groups)!=5 or [group['index'] for group in groups[:2]]!=[0,1]:
            raise relation.RelationError('ownership first original partition exact two precompute groups')
        for group in groups[:2]:
            for stage in full['stages'][group['stage_start']:group['stage_end']]:
                earlier.update(stage['rows'])
        earlier.update(full['constant_rows'])
    selected={row['row']:row for row in extracted['selected_rows']}
    def rows(indices):
        if not indices<=selected.keys():
            raise relation.RelationError('ownership partition row missing retained selection')
        return [selected[index] for index in sorted(indices)]
    result=row_partition(rows(originals),rows(earlier),rows(set(local['local_rows'])),
        domain_size=checked['metadata']['domain_size'],full_rows=checked['metadata']['full_rows'])
    return {**result,'window_index':local['window_index']}
