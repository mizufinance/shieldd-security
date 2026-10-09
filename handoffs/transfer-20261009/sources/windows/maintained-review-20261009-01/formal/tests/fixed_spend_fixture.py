"""Mathematical typed fixtures, never observations of a runtime Transfer."""
import copy
import io
from blake3 import blake3
from circuits import transfer_fixed_spend as fixed, transfer_relation as relation
from circuits import transfer_authorization_roles as roles
from circuits.transfer_balance_rows import canonical, combine, source_index
from tests import test_transfer_fixed_spend as fixtures
from tests import test_transfer_fixed_spend_rows as rows_fixture
from tests import test_transfer_authorization_roles as rf


def full_fixture(ordered_canonical=False, ordered_fixed=False):
    ordered_canonical=ordered_canonical or ordered_fixed
    template,accepted=fixtures.fixture()
    domain,constant=16384,16000
    template.update(domain_size=domain,constant_copy=constant)
    accepted['metadata'].update(domain_size=domain,constant_copy=constant)
    expressions={tuple(item['source']):copy.deepcopy(item) for item in template['expressions']}
    if ordered_canonical:
        # Typed compiler-allocation variant only, never a runtime observation.
        # Interleave each canonical carry and its actual square auxiliary.
        for item in expressions.values():
            for term in item['terms']:
                if 501<=term[0]<=751:term[0]=6000+2*(term[0]-501)
    generator=rows_fixture.curve_fixture()
    native=lambda point:[rf.native(v) for v in point]
    template['generator']=native(generator)
    accepted['metadata']['spend']['generator']=native(generator)
    serial=0
    def node(lc):
        nonlocal serial
        serial+=1;handle=(2,20000+serial)
        expressions[handle]=dict(source=list(handle),terms=[[c,f'{v:064x}'] for c,v in canonical(lc)])
        return {'source':list(handle)}
    def variable(column=None):return node([(3000+serial if column is None else column,1)])
    def lc(ref):
        if 'native' in ref:return canonical([(0,int(ref['native'],16))])
        return tuple((c,int(v,16)) for c,v in expressions[source_index(ref['source'])]['terms'])
    before=[rf.native(0),rf.native(1)];base=generator;windows=[]
    for i in range(126):
        twice=fixed._add(base,base);triple=fixed._add(twice,base);next_base=fixed._add(twice,twice)
        high=8000 if i==0 else 8004+16*(i-1)
        selected=([variable(high),variable(high+2)] if ordered_fixed else [variable(),variable()])
        if i==0:
            arithmetic=[rf.native(0),selected[1],node(combine(*map(lc,selected))),rf.native(0)]
            after=selected if not ordered_fixed else []
        else:
            arithmetic=([variable(high+4+2*axis) for axis in range(4)] if ordered_fixed else
                        [variable() for _ in range(4)])
            after=[]
        if i!=0 or ordered_fixed:
            for axis in range(2):
                handle=(1,(1997 if ordered_fixed else 5000)+2*i+axis)
                expressions[handle]=dict(source=list(handle),terms=[[3+handle[1],f'{1:064x}']])
                after.append({'source':list(handle)})
        xx,yy,summed,xy=map(lc,arithmetic)
        numerator=[node(combine(combine(summed,xx,-1),yy,-1)),node(combine(yy,xx))]
        denominator=[node(combine(((0,1),),canonical((c,v*fixed.D) for c,v in xy))),
                     node(combine(((0,1),),canonical((c,v*fixed.D) for c,v in xy),-1))]
        windows.append(dict(bits=template['bits'][2*i:2*i+2],table=list(map(native,(base,twice,triple,next_base))),
            points=[before,selected,after],arithmetic=arithmetic,quotient=numerator+denominator+after))
        before,base=after,next_base
    for ref,last in zip(template['output'],before):
        handle=source_index(ref['source']);expressions[handle]=dict(source=list(handle),terms=[[c,f'{v:064x}'] for c,v in lc(last)])
        for item in accepted['metadata']['expressions']:
            if item['source']==list(handle):item['terms']=copy.deepcopy(expressions[handle]['terms'])
    windows[-1]['points'][2]=template['output'];windows[-1]['quotient'][4:]=template['output']
    def reaccept(role_obj):
        base_fixture=rf.AuthorizationRoleTests();base_fixture.setUp()
        rnk,ivk=base_fixture.rnk,base_fixture.ivk
        rnk.update(relation_digest=role_obj['relation_digest'],domain_size=domain,
                   full_rows=role_obj['full_rows'],constant_copy=constant)
        ivk.update(relation_digest=role_obj['relation_digest'],domain_size=domain,
                   stored_rows=role_obj['full_rows'],constant_copy=constant)
        return roles.inspect_metadata(rf.encoded(role_obj),role_obj['relation_digest'],role_obj['ivk_handles'],rnk,ivk)
    accepted=reaccept(accepted['metadata'])
    objects=[];checks=[]
    for start in range(0,126,16):
        obj=copy.deepcopy(template);obj.update(window_start=start,window_count=min(16,126-start),windows=windows[start:start+16])
        required={source_index(bit) for bit in obj['bits']}|{source_index(obj['canonical']['endpoint'])}
        def visit(value):
            if isinstance(value,dict):
                if set(value)=={'source'}:required.add(source_index(value['source']))
                else:
                    for v in value.values():visit(v)
            elif isinstance(value,list):
                for v in value:visit(v)
        for key in ('randomizer','output','canonical','windows'):visit(obj[key])
        obj['expressions']=[expressions[h] for h in sorted(required)]
        checks.append(fixed.inspect_metadata(rf.encoded(obj),accepted));objects.append(obj)
    fixed.join_chunks(checks)
    rows=[]
    def row(a,b=()):rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in canonical(a)],b=[[c,f'{v:064x}'] for c,v in canonical(b)]))
    required={};products=[];squares=[]
    for i,checked in enumerate(checks):
        r,p,s=fixed._requirements(checked,i==0);required.update(r);products.extend(p);squares.extend(s)
    assert not squares
    for a,b in required:row(a,b)
    for i,(role,minus,plus,out,numerator) in enumerate(products):
        auxiliary=((7000+i,1),);output=out if out is not None else ((9000+i,1),)
        if ordered_fixed and role.startswith('window.'):
            window=int(role.split('.')[1]);high=8000 if window==0 else 8004+16*(window-1)
            if out is None:
                axis=int(role.split('.')[-1]);output=((high+12+2*axis,1),)
            auxiliary=((max(column for column,_ in output if column!=constant)+1,1),)
        if ordered_canonical and role.startswith('canonical.'):
            auxiliary=((output[0][0]+1,1),)
        row(minus,auxiliary);row(plus,combine(auxiliary,output,4))
        if numerator is not None:row(combine(output,numerator,-1))
    # The same synthetic ordinary stream also contains the final captured
    # AK/contribution addition and computed/RK equalities. These are row data,
    # not invented intermediate source observations.
    outline=lambda lc:canonical((constant if c==0 else c,v) for c,v in lc)
    role_lcs={tuple(item['source']):tuple((c,int(v,16)) for c,v in item['terms'])
              for item in accepted['metadata']['expressions']}
    spend=accepted['metadata']['spend']
    left,right,computed,rk=(tuple(role_lcs[source_index(v['source'])] for v in spend[key])
                           for key in ('ak','contribution','computed','rk'))
    def add_product(a,b,out,aux):
        row(outline(combine(a,b,-1)),[(aux,1)])
        row(outline(combine(a,b)),combine(((aux,1),),out,4))
    xx,yy,summed,xy=[((c,1),) for c in range(13000,13004)]
    for i,(a,b,out) in enumerate(((left[0],right[0],xx),(left[1],right[1],yy),
                                 (combine(*left),combine(*right),summed),(xx,yy,xy))):
        add_product(a,b,out,13100+i)
    ns=[combine(combine(summed,xx,-1),yy,-1),combine(yy,xx)]
    ds=[combine(((0,1),),((13003,fixed.D),)),combine(((0,1),),((13003,fixed.D),),-1)]
    for i in range(2):
        out=((13200+i,1),);add_product(computed[i],ds[i],out,13300+i)
        row(outline(combine(out,ns[i],-1)));row(outline(combine(computed[i],rk[i],-1)))
    public,block=[[1,900]],[[1,901]]
    digest=blake3(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+relation.indices(public)+relation.u64(1)+relation.indices(block))
    for record in rows:digest.update(b'A'+relation.terms(record['a'],domain)+b'B'+relation.terms(record['b'],domain))
    identity=digest.hexdigest()
    role_obj=accepted['metadata'];role_obj.update(relation_digest=identity,full_rows=len(rows))
    accepted=reaccept(role_obj)
    for obj in objects:obj.update(relation_digest=identity,full_rows=len(rows))
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity,
        domain_size=domain,stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,
        public_columns=[1],committed_columns=[[2]],source_public=public,source_blocks=[block],
        coefficient_encoding='canonical-big-endian-32',field_modulus=str(fixed.P),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
        padding='implicit-all-zero-rows-to-domain-size')
    stream=b''.join(rf.encoded(item) for item in [header,*rows,dict(eof=True,rows=len(rows))])
    return [rf.encoded(obj) for obj in objects],accepted,stream
