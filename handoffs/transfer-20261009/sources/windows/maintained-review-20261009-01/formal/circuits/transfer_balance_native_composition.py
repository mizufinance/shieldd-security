"""Exact variable/H/final constructor frame join after the ONE joint replay.

This checks original rows and assignment ownership, not native mathematical
equality. Native AssetMap seed reuse, scalar/codec and named VALUE_BLINDING
object association must be proved on this same assignment. No second stream,
capture schema, endpoint assertion or qualification flag is introduced.
"""
from . import transfer_relation as relation
from . import transfer_balance_variable_program as variable
from . import transfer_balance_blinding_program as blinding
from . import generate_transfer_balance_final_add_completion as final_renderer
from . import transfer_balance_final_add as final
from . import transfer_remaining_pages as remaining
from . import transfer_balance_input_layout as layout


def _rows(selections):
    rows = {}
    for selected in selections:
        for row in selected['selected_rows']:
            index = row['row']
            relation.natural(index,200770)
            value = tuple(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
            if index in rows and rows[index] != value:
                raise relation.RelationError('balance native shared original polynomial changed')
            rows[index] = value
    if not rows or len(rows)>32768:
        raise relation.RelationError('balance native bounded original rows required')
    return rows


def _support(rows,indices):
    if not set(indices)<=rows.keys():
        raise relation.RelationError('balance native missing earlier original row')
    return {column for index in indices for side in rows[index] for column,_ in side}


def _join(v,b,f,rows,identity):
    """Pure reviewed row/write boundary; never accepts a qualification itself."""
    for component in (v,b,f):
        if component['identity']!=identity:
            raise relation.RelationError('balance native one exact original relation identity')
    if len(v['programs'])!=65 or len(b['loop']['programs'])!=126:
        raise relation.RelationError('balance native exact65/126 constructor coverage')
    shared={0,1,2,6,9,200692}
    seed=set(v['seed_writes'])
    # The seed's two actual coordinates can already be the preceding map
    # output. They must be reused by semantic equality, not counted as fresh
    # overwrites preserving earlier map rows by an absent-column argument.
    vw=set(v['writes'])-seed
    bw=set(b['canonical']['writes'])|set(b['loop']['writes'])
    fw=set(f['writes'])
    if (vw|bw|fw|seed)&shared:
        raise relation.RelationError('balance native assignment writes shared original column')
    if seed & (vw|bw|fw) or vw & (bw|fw) or bw & fw:
        raise relation.RelationError('balance native constructor writes overlap')
    # The sign/magnitude and other shared inputs are earlier constructed
    # roles even when no variable-window polynomial happens to read them.
    # In particular H must not destroy the sign consumed by the final add.
    protected=set(v['protected'])
    if (bw|fw)&protected:
        raise relation.RelationError('balance native H/final writes destroy earlier signed/shared roles')
    vr=set(v['rows']);br=set(b['loop']['rows'])|set(b['canonical']['rows']);fr={row['row'] for row in f['selected_rows']}
    vs=_support(rows,vr);bs=_support(rows,br)
    if bw&vs:
        raise relation.RelationError('balance native H writes destroy variable original rows')
    if fw&(vs|bs):
        raise relation.RelationError('balance native final writes destroy preceding original rows')
    # Exact endpoint source LCs were separately derived from all three genuine
    # qualifiers by from_ingress. Here they are tied to the constructed loops.
    page=v['checked']['chunks'][-1]
    def observe(value):
        if value[0]!='source' or value[1] not in page['derived']:
            raise relation.RelationError('balance native exact actual outgoing source LC')
        return page['derived'][value[1]]
    unsigned=tuple(observe(value) for value in v['programs'][-1]['outgoing'])
    blinded=b['loop']['programs'][-1]['output']
    if unsigned!=f['roles']['unsigned'] or blinded!=f['roles']['blinded']:
        raise relation.RelationError('balance native exact loop/final source LC continuity')
    held={c for terms in (f['roles']['negative'],*unsigned,*blinded) for c,_ in terms}
    if fw&held:
        raise relation.RelationError('balance native final overwrites its earlier native endpoint')
    # The variable collector also retains the already decomposed magnitude's
    # Boolean rows. They belong to the earlier signed constructor, never to
    # this loop's newly owned rows. Preserve their exact original polynomials.
    initial=set(rows)-(vr|br|fr)
    if (vw|bw|fw)&_support(rows,initial):
        raise relation.RelationError('balance native writes destroy retained incoming original rows')
    return dict(identity=identity,parents=f['parents'],incoming_rows=sorted(initial),variable_rows=sorted(vr),
        blinding_rows=sorted(br),final_rows=sorted(fr),rows=sorted(rows),
        seed_columns=sorted(seed),variable_writes=sorted(vw),blinding_writes=sorted(bw),
        final_writes=sorted(fw),shared=sorted(shared),protected=sorted(protected),unsigned=unsigned,blinded=blinded,
        seed_strategy='Reuse preceding proved native map coordinates on the SAME assignment; semantic identity required, no fresh seed/frame claim',
        scope='Checked exact65/126/final original row continuity and cross-constructor outside frames only; native seed/scalar/H object and whole Transfer joins OPEN')


def plan(variable_parent,variable_pages,blinding_parent,blinding_pages,
         caller_parent,caller_page,accepted_roles,signed,asset_base,blinding_base,
         joint,readonly_lcs=()):
    """Conditional callable from genuine parents and retained joint row data.

    The lifecycle integer is mandatory but never a proof of production replay.
    Root must bind this invocation to the qualification/ordinary2/repeat and
    unchanged private-binary replay receipts. No stream is opened here.
    """
    if (not isinstance(joint,dict) or type(joint.get('ordinary_replays')) is not int or
            joint['ordinary_replays']!=1):
        raise relation.RelationError('balance native retained ONE joint replay required')
    associated=final.from_ingress(variable_parent,variable_pages,blinding_parent,blinding_pages,
        caller_parent,caller_page,accepted_roles,signed,asset_base,blinding_base)
    if joint.get('parents')!=associated:
        raise relation.RelationError('balance native exact genuine joint source/parent views')
    layout.render(joint.get('input_layout'))
    if joint['input_layout']['identity']!=joint['identity']:
        raise relation.RelationError('balance native committed shadow same replay identity')
    caller=remaining.inspect_page(caller_parent,caller_page,0,accepted_roles)
    scalar_ref=caller['records']['caller','shared',0][6]
    v=variable.plan(variable_parent,variable_pages,final.DIGEST,signed,asset_base,
        joint['variable'],readonly_lcs)
    b=blinding.plan(blinding_parent,blinding_pages,blinding_base,scalar_ref,
        joint['blinding'],readonly_lcs)
    f=joint['final_add']
    if f['roles']!=associated['roles']:
        raise relation.RelationError('balance native final genuine source roles changed')
    final_renderer._recheck(f)
    rows=_rows([*v['selections'],joint['blinding']['canonical']['certificate'],
        joint['blinding']['fixed'],joint['input_layout'],{'selected_rows':f['selected_rows']}])
    return _join(v,b,f,rows,joint['identity'])
