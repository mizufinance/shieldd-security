"""One complete ordinary replay for retained, typed IVK/reduction/RNK exports.

Row identity is checked at every requested physical index, before any candidate
is emitted. Parent source/LC/parameter/recurrence acceptance is independent of
this check. This does not qualify new runtime observations or kernel results.
"""
import hashlib,json
from . import transfer_relation as relation
from . import generate_transfer_prefix_hash_completion as hashes
from . import transfer_ivk_reduction_completion as reduction
from . import transfer_rnk_hash as rnk


def _demand(parts, domain, count):
    rows={};uses={}
    for name,records in parts:
        if not isinstance(records,list) or not 1<=len(records)<=8192:
            raise relation.RelationError('prefix retained row bound')
        previous=-1
        for row in records:
            if not isinstance(row,dict) or set(row)!={'row','a','b'}:
                raise relation.RelationError('prefix retained row closed shape')
            index=relation.natural(row['row'],count)
            if index<=previous:raise relation.RelationError('prefix retained rows unordered/duplicate')
            previous=index
            for key in ('a','b'):relation.terms(row[key],domain)
            if index in rows and rows[index]!=row:
                raise relation.RelationError('prefix conflicting shared original row')
            rows[index]=row;uses.setdefault(index,[]).append(name)
    if len(rows)>16384 or sum(len(row['a'])+len(row['b']) for row in rows.values())>262144:
        raise relation.RelationError('prefix combined finite row/term bound')
    return rows,uses


def replay_rows(parts,stream,expected_relation,domain,count):
    """Exact row comparison plus complete framing/digest/EOF, once per input."""
    wanted,uses=_demand(parts,domain,count);seen=set()
    def observe(row):
        index=row['row']
        if index in wanted:
            if row!=wanted[index]:raise relation.RelationError('prefix actual original row mismatch')
            seen.add(index)
    identity=relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size']!=domain or identity['stored_rows']!=count or seen!=set(wanted):
        raise relation.RelationError('prefix original relation shape/coverage mismatch')
    return dict(identity=identity,rows=len(wanted),row_uses={str(i):uses[i] for i in sorted(uses)},
        selected_rows_sha256=hashlib.sha256(json.dumps([wanted[i] for i in sorted(wanted)],
            sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        scope='exact original row membership; source/key/kernel/full prefix completion separate')


def replay(ivk_data,ivk_export,reduction_data,reduction_export,rnk_data,rnk_export,
           parameter_root,expected_relation,ivk_handles,rnk_bindings,readonly_lcs,stream):
    """Reaccept typed parents and verify all selected rows in one full stream.

    Callers must separately reaccept the role capture and derive ivk_handles /
    rnk_bindings from it; these are existing accepted-ingress boundary inputs.
    """
    ivk_selected,metadata,_=hashes.select_ivk(ivk_data,ivk_export,parameter_root,expected_relation,readonly_lcs)
    checked_ivk=hashes.ivk.inspect_metadata(ivk_data,parameter_root,expected_relation)
    if checked_ivk['metadata']['handles']!=ivk_handles:
        raise relation.RelationError('prefix accepted IVK handle alias')
    reduction_plan=reduction.plan(reduction_data,checked_ivk,reduction_export,expected_relation,readonly_lcs)
    parts=[('ivk',[dict(row=r['index'],a=r['a'],b=r['b']) for r in ivk_export['rows']]),
           ('reduction',reduction_export['selected_rows'])]
    for block in range(3):
        # Recompute physical recurrence against exact upstream round constants;
        # the retained derivative is never trusted just because a digest agrees.
        selected=rnk.row_permutation_selection(rnk_data,rnk_export,block,parameter_root,
            expected_relation,ivk_handles,rnk_bindings)
        hashes.validate_selected(selected,metadata)
        if selected['outline']!=metadata['constant_copy']:
            raise relation.RelationError('prefix shared RNK constant role alias')
        parts.append(('rnk'+str(block),rnk_export['blocks'][block]['selected_rows']))
    result=replay_rows(parts,stream,expected_relation,metadata['domain_size'],metadata['stored_rows'])
    result.update(schema='shieldd-prefix-constructor-row-replay-v1',
        parents={key:hashlib.sha256(data).hexdigest() for key,data in
            (('ivk',ivk_data),('reduction',reduction_data),('rnk',rnk_data))},
        reduction_products=[len(phase['stages']) for phase in reduction_plan['phases']],
        reduction_inverse_assertion_reversed=reduction_plan['inverse']['assertion_reversed'])
    return result
