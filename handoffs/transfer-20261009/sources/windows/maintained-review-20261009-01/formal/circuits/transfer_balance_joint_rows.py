"""One original replay for genuine variable5/blinding8/canonical/final-add roles.

This is an additive row collector, not another CLI or a capture qualifier.
Every projection retains physical indices and reuses its semantic validators.
Actual source parents/ordinary2/repeat are required before the first row read.
"""
import json
from . import transfer_balance_variable as variable, transfer_balance_variable_batch as variables
from . import transfer_balance_blinding_fixed as blinding, transfer_balance_blinding_batch as blindings
from . import transfer_balance_blinding_canonical as canonical_rows, transfer_balance_final_add as addition
from . import transfer_arithmetic as arithmetic, transfer_relation as relation
from .transfer_epk_fixed_canonical import _CandidateStream
from . import transfer_balance_input_layout as input_layout
from . import transfer_balance_shared_add as shared_add


class _RowTap:
    """Forward exact bytes; bounded observer sees every physical row once."""
    def __init__(self,stream,observer):
        self.stream,self.observer=stream,observer
        self.header=False;self.eof=False;self.tail=False;self.next_row=0

    def readline(self):
        if self.eof:raise relation.RelationError('joint balance read after EOF')
        line=self.stream.readline();obj=relation.record(line)
        if not self.header:
            if obj.get('schema')!='shieldd-transfer-relation-v1':
                raise relation.RelationError('joint balance original header required')
            self.header=True
        elif set(obj)=={'eof','rows'}:
            if obj['eof'] is not True or type(obj['rows']) is not int or obj['rows']!=self.next_row:
                raise relation.RelationError('joint balance exact EOF count')
            self.eof=True
        else:
            if set(obj)!={'row','a','b'} or type(obj['row']) is not int or obj['row']!=self.next_row:
                raise relation.RelationError('joint balance exact original row order')
            self.next_row+=1;self.observer(obj)
        return line

    def read(self,size):
        if size!=1 or not self.eof or self.tail:raise relation.RelationError('joint balance exact tail lifecycle')
        self.tail=True;return self.stream.read(size)


def _merge(groups):
    required={};products=[];squares=[]
    for prefix,(direct,ps,ss) in groups:
        for row,names in direct.items():required.setdefault(row,[]).extend(prefix+name for name in names)
        products.extend((prefix+role,*operands) for role,*operands in ps)
        squares.extend((prefix+role,*operands) for role,*operands in ss)
    return required,products,squares


def _project(combined,prefix):
    if prefix not in ('variable.','blinding.'):
        raise relation.RelationError('joint balance exact component prefix')
    templates=[dict(row=item['row'],roles=[name[len(prefix):] for name in item['roles'] if name.startswith(prefix)])
        for item in combined['templates'] if any(name.startswith(prefix) for name in item['roles'])]
    products=[dict(role=item['role'][len(prefix):],rows=item['rows'])
        for item in combined['products'] if item['role'].startswith(prefix)]
    indices={item['row'] for item in templates}|{index for item in products for index in item['rows']}
    records=combined['selected_rows']
    if (not isinstance(records,list) or not 1<=len(records)<=32768 or
        any(type(row.get('row')) is not int for row in records) or
        [row['row'] for row in records]!=sorted({row['row'] for row in records})):
        raise relation.RelationError('joint balance original bounded ordered unique row union')
    rows={row['row']:row for row in records}
    if not indices or not indices<=rows.keys():
        raise relation.RelationError('joint balance projected physical row missing')
    return dict(identity=combined['identity'],templates=templates,products=products,
                selected_rows=[rows[i] for i in sorted(indices)])


def extract_rows(stream,variable_parent,variable_pages,blinding_parent,blinding_pages,
                 caller_parent,caller_page,accepted_roles,signed,asset_base,blinding_base,
                 readonly_lcs=()):
    """Root-only one full production stream, no additional compile/capture."""
    source=addition.from_ingress(variable_parent,variable_pages,blinding_parent,blinding_pages,
        caller_parent,caller_page,accepted_roles,signed,asset_base,blinding_base)
    v=variable.inspect_pages(variable_parent,variable_pages,addition.DIGEST,signed,asset_base)
    # The actual caller scalar source was independently tied in from_ingress.
    from . import transfer_remaining_pages as remaining
    c=remaining.inspect_page(caller_parent,caller_page,0,accepted_roles)
    scalar_ref=c['records']['caller','shared',0][6]
    b=blinding.inspect_pages(blinding_parent,blinding_pages,blinding_base,scalar_ref)
    matcher=shared_add.Matcher(source['roles'])
    row_tap=_RowTap(stream,matcher.observe)
    canonical_tap=_CandidateStream(row_tap,[canonical_rows.boundary(b)],200692)
    requirements=_merge([('variable.',variables._requirements(v,True)),('blinding.',blindings.requirements(b)),
                         ('layout.',input_layout.requirements())])
    combined=arithmetic.extract_templates(canonical_tap,addition.DIGEST,262144,200770,*requirements,label='joint-balance')
    if not canonical_tap.eof or not canonical_tap.tail_checked or not row_tap.eof or not row_tap.tail:
        raise relation.RelationError('joint balance unchanged full ordinary EOF lifecycle')
    identity=combined['identity']
    if identity['source_public']!=[[1,22734]] or identity['source_blocks']!=[[[1,6]]]:
        raise relation.RelationError('joint balance original production source layout')
    fixed=canonical_rows._fixed_projection(b,_project(combined,'blinding.'))
    scalar=canonical_rows._derive(b,identity,canonical_tap.raw,canonical_tap.normalized,canonical_tap.records)
    return dict(variable=variables._partition(v,_project(combined,'variable.'),True),
        blinding=dict(fixed=fixed,canonical=scalar,parent_sha256=b['parent_sha256'],
            raw_page_sha256=b['raw_page_sha256'],ordinary_replays=1,
            scope='Genuine fixed126/canonical252 projections from joint ordinary replay'),
        final_add=matcher.finish(identity,readonly_lcs),input_layout=input_layout.selected(combined),
        identity=identity,ordinary_replays=1,
        parents=source,scope='One full original replay, exact variable65/blinding126/canonical252/final-add row projections; native/legal/frame/Transfer completeness OPEN')


def reaccept_retained(extraction,variable_parent,variable_pages,blinding_parent,blinding_pages,
                      caller_parent,caller_page,accepted_roles,signed,asset_base,blinding_base,
                      readonly_lcs=()):
    """Recheck a root-pinned completed projection with revised outside frames.

    The caller must bind the actual saved extraction and its original input
    receipts. This function performs no ordinary replay and claims none. The
    component constructors still check their original rows independently.
    """
    if (not isinstance(extraction,dict) or set(extraction)!={'variable','blinding','final_add',
            'input_layout','identity','ordinary_replays','parents','scope'} or
            type(extraction['ordinary_replays']) is not int or extraction['ordinary_replays']!=1):
        raise relation.RelationError('completed retained joint projection required')
    source=addition.from_ingress(variable_parent,variable_pages,blinding_parent,blinding_pages,
        caller_parent,caller_page,accepted_roles,signed,asset_base,blinding_base)
    # Stored JSON uses lists for tuples. Compare the exact serialization shape
    # before the independently checked row/LC validators run.
    if extraction['parents']!=json.loads(json.dumps(source)):
        raise relation.RelationError('retained projection actual semantic parents differ')
    input_layout.public_witness_shadows(extraction['identity'])
    original=extraction['final_add']
    if not isinstance(original,dict) or original.get('identity')!=extraction['identity']:
        raise relation.RelationError('retained final original identity differs')
    matcher=shared_add.Matcher(source['roles'])
    for row in original.get('selected_rows',[]):matcher.observe(row)
    replacement=matcher.finish(extraction['identity'],readonly_lcs)
    # Frame protection may be corrected, never the original row witnesses,
    # native source roles, discovered arithmetic or owned writes.
    if json.loads(json.dumps({k:v for k,v in replacement.items() if k!='protected'}))!={
            k:v for k,v in original.items() if k!='protected'}:
        raise relation.RelationError('retained final arithmetic or original rows differ')
    # Restore the independently re-parsed typed view after exact stored-shape
    # comparison. Downstream continuity checks use canonical LC tuples.
    return dict(extraction,final_add=replacement,parents=source)
