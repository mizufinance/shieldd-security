"""Synthetic typed row fixtures only; never a real Transfer observation."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_fixed_spend as fixed, generate_transfer_fixed_spend as generate
from circuits import transfer_authorization_roles as roles, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests import test_transfer_fixed_spend as fixtures
from tests import test_transfer_authorization_roles as role_fixtures


def curve_fixture():
    """A mathematical nontrivial curve point, unrelated to the actual generator."""
    p=fixed.P
    x=next(x for x in range(1,64) if pow((1+x*x)*pow(1-fixed.D*x*x,-1,p)%p,(p-1)//2,p)==1)
    square=(1+x*x)*pow(1-fixed.D*x*x,-1,p)%p
    odd=p-1;power=0
    while odd%2==0:odd//=2;power+=1
    nonresidue=next(z for z in range(2,128) if pow(z,(p-1)//2,p)==p-1)
    c=pow(nonresidue,odd,p);y=pow(square,(odd+1)//2,p);t=pow(square,odd,p)
    while t!=1:
        i=1;probe=t*t%p
        while probe!=1:probe=probe*probe%p;i+=1
        b=pow(c,1<<(power-i-1),p);y=y*b%p;t=t*b*b%p;c=b*b%p;power=i
    assert y*y%p==square
    return x,y


def fixture(*, changed=None, window_start=0):
    obj,accepted=fixtures.fixture();obj['domain_size']=2048;obj['constant_copy']=1900
    generator=curve_fixture();twice=fixed._add(generator,generator);triple=fixed._add(twice,generator)
    native=lambda point:[role_fixtures.native(v) for v in point]
    one=role_fixtures.native(1);zero=role_fixtures.native(0)
    sx,sy=role_fixtures.source(2,600),role_fixtures.source(2,601)
    sum_ref=role_fixtures.source(2,602)
    obj['generator']=native(generator)
    obj['windows'][0].update(table=list(map(native,(generator,twice,triple,fixed._add(twice,twice)))),
        points=[[zero,one],[sx,sy],[sx,sy]],arithmetic=[zero,sy,sum_ref,zero],
        quotient=[sx,sy,one,one,sx,sy])
    expressions={tuple(item['source']):item for item in obj['expressions']}
    for handle,lc in [((2,600),((400,1),)),((2,601),((401,1),)),((2,602),((400,1),(401,1)))]:
        expressions[handle]=dict(source=list(handle),terms=[[c,f'{v:064x}'] for c,v in lc])
    obj['expressions']=[expressions[index] for index in sorted(expressions)]
    accepted['metadata']['spend']['generator']=copy.deepcopy(obj['generator'])
    accepted['metadata'].update(domain_size=2048,constant_copy=1900)
    if window_start==1:
        expressions.pop((2,602))
        obj['window_start']=1;obj['windows'][0]['bits']=copy.deepcopy(obj['bits'][2:4])
        weighted=fixed._add(twice,twice);weighted_twice=fixed._add(weighted,weighted)
        obj['windows'][0]['table']=list(map(native,(weighted,weighted_twice,
            fixed._add(weighted_twice,weighted),fixed._add(weighted_twice,weighted_twice))))
        def source(index,terms):
            expressions[(2,index)]=dict(source=[2,index],terms=[[c,f'{v:064x}'] for c,v in canonical(terms)])
            return role_fixtures.source(2,index)
        before=[source(603,[(404,1)]),source(604,[(405,1)])]
        xx=source(620,[(420,1)]);yy=source(621,[(421,1)])
        summed=source(622,[(422,1)]);xy=source(623,[(423,1)])
        numerator=[source(624,[(422,1),(420,-1),(421,-1)]),source(625,[(420,1),(421,1)])]
        denominator=[source(626,[(0,1),(423,fixed.D)]),source(627,[(0,1),(423,-fixed.D)])]
        qx,qy=role_fixtures.source(1,500),role_fixtures.source(1,501)
        for witness in (500,501):expressions[(1,witness)]=dict(source=[1,witness],terms=[[3+witness,f'{1:064x}']])
        obj['windows'][0].update(points=[before,[sx,sy],[qx,qy]],arithmetic=[xx,yy,summed,xy],
                                  quotient=[*numerator,*denominator,qx,qy])
        obj['expressions']=[expressions[index] for index in sorted(expressions)]
    checked=fixed.inspect_metadata(role_fixtures.encoded(obj),accepted)
    required,products,squares=fixed._requirements(checked,True)
    assert not squares
    rows=[]
    def row(a,b=()):
        rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in canonical(a)],
                         b=[[c,f'{v:064x}'] for c,v in canonical(b)]))
    for a,b in required:row(a,b)
    for offset,(role,minus,plus,out,numerator) in enumerate(products):
        auxiliary=((1100+offset,1),)
        output=out if out is not None else ((1600+offset,1),)
        row(minus,auxiliary);row(plus,combine(auxiliary,output,4))
        if numerator is not None:row(combine(output,numerator,-1))
    if changed:
        changed(rows,checked,required,products)
    domain=obj['domain_size'];public=[[1,900]];block=[[1,901]]
    digest=blake3(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+
                  relation.indices(public)+relation.u64(1)+relation.indices(block))
    for record in rows:digest.update(b'A'+relation.terms(record['a'],domain)+b'B'+relation.terms(record['b'],domain))
    identity=digest.hexdigest();obj.update(relation_digest=identity,full_rows=len(rows))
    role_obj=copy.deepcopy(accepted['metadata']);role_obj.update(relation_digest=identity,full_rows=len(rows))
    base=role_fixtures.AuthorizationRoleTests();base.setUp()
    rnk=base.rnk;ivk=base.ivk
    rnk.update(relation_digest=identity,domain_size=domain,full_rows=len(rows),constant_copy=1900)
    ivk.update(relation_digest=identity,domain_size=domain,stored_rows=len(rows),constant_copy=1900)
    accepted=roles.inspect_metadata(role_fixtures.encoded(role_obj),identity,role_obj['ivk_handles'],rnk,ivk)
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity,
        domain_size=domain,stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,
        public_columns=[1],committed_columns=[[2]],source_public=public,source_blocks=[block],
        coefficient_encoding='canonical-big-endian-32',field_modulus=str(fixed.P),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
        padding='implicit-all-zero-rows-to-domain-size')
    encode=role_fixtures.encoded
    stream=io.BytesIO(b''.join(encode(item) for item in [header,*rows,dict(eof=True,rows=len(rows))]))
    return encode(obj),accepted,stream


def synthetic_candidates():
    data,accepted,stream=fixture();extracted=fixed.extract_rows(data,accepted,stream)
    return dict(RuntimeFixedSpendWindow000=generate.generate_window(data,accepted,extracted),
                RuntimeFixedSpendChunk000=generate.generate_chunk(data,accepted,extracted),
                RuntimeTransferRandomizer=generate.generate_canonical(data,accepted,extracted))


class FixedSpendRowTests(unittest.TestCase):
    def test_exact_actual_templates_and_products(self):
        args=fixture();extracted=fixed.extract_rows(*args)
        self.assertEqual(len(extracted['products']),253)
        self.assertEqual(len(extracted['templates']),255)

    def test_semantically_changed_product_bit_reconstruction_endpoint_refuse(self):
        for target in ('product','boolean0','reconstruction','endpoint'):
            def corrupt(rows,checked,required,products):
                index=len(required) if target=='product' else next(i for i,key in enumerate(required) if target in required[key])
                rows[index]['a']=[];rows[index]['b']=[]
            with self.subTest(target=target),self.assertRaisesRegex(relation.RelationError,'missing fixed'):
                fixed.extract_rows(*fixture(changed=corrupt))

    def test_complete_stream_digest_is_required(self):
        data,accepted,stream=fixture();raw=stream.getvalue().replace(f'{1:064x}'.encode(),f'{2:064x}'.encode(),1)
        with self.assertRaisesRegex(relation.RelationError,'relation digest'):
            fixed.extract_rows(data,accepted,io.BytesIO(raw))

    def test_persisted_selection_and_finite_named_audits(self):
        data,accepted,stream=fixture();extracted=fixed.extract_rows(data,accepted,stream)
        extracted=json.loads(json.dumps(extracted))
        window=generate.generate_window(data,accepted,extracted)
        chunk=generate.generate_chunk(data,accepted,extracted)
        scalar=generate.generate_canonical(data,accepted,extracted)
        self.assertIn('import ShielddSecurity.ScalarBits\n',window)
        self.assertNotIn('LinearCombination',window)
        self.assertIn('noncomputable def window ',window)
        self.assertIn('noncomputable def windows ',chunk)
        for definition in window.splitlines():
            if definition.startswith(('def hi0 ', 'def hi1 ')):
                self.assertNotIn('--',definition)
                self.assertIn(' - (',definition)
        self.assertIn('have sumleft := Compiler.canonical_equal',window)
        self.assertIn('have sumright := Compiler.canonical_equal',window)
        for source,names in [(window,('actual_arithmetic','fixed_equations','actual_window_coordinates')),
                             (chunk,('actual_trace','actual_chunk_coordinates')),
                             (scalar,('checked_endpoint','checked_reconstruction','actual_randomizer_canonical'))]:
            self.assertIn('maxHeartbeats 500000',source)
            self.assertNotIn('sorry',source);self.assertNotIn('native_decide',source)
            for name in names:
                self.assertIn('#check @'+name,source);self.assertIn('#print axioms '+name,source)

    def test_generator_refuses_changed_retained_row(self):
        data,accepted,stream=fixture();extracted=fixed.extract_rows(data,accepted,stream)
        extracted['selected_rows'][-1]['a']=[]
        with self.assertRaises(relation.RelationError):generate.generate_canonical(data,accepted,extracted)

    def test_nonlinear_quotients_retain_assertions_and_constructive_transport(self):
        data,accepted,stream=fixture(window_start=1);extracted=fixed.extract_rows(data,accepted,stream)
        source=generate.generate_window(data,accepted,extracted)
        for axis in range(2):
            self.assertIn('#check @complete_quotient'+str(axis),source)
        self.assertIn('GroupRowCompletion.original_rows_complete',source)
        self.assertIn('(legal : eval rho',source)
        self.assertIn('rho 1900 = rho 0',source)
        def corrupt(rows,checked,required,products):
            rows[-1]['a']=[];rows[-1]['b']=[]
        with self.assertRaisesRegex(relation.RelationError,'materialized product/assertion'):
            fixed.extract_rows(*fixture(window_start=1,changed=corrupt))


if __name__=='__main__':unittest.main()
