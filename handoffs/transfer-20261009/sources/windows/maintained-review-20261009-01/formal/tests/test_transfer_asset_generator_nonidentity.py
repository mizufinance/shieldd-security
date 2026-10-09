"""One small owned map fixture plus independent final inverse original rows."""
import copy,io,json,unittest
from blake3 import blake3
from circuits import transfer_asset_generator_nonidentity as generator,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_asset_map import fixture,encoded,P


def inverse_fixture(reverse=False):
    data,caller,stream,rows,b=fixture(17);obj=json.loads(data)
    q=3+b.next_witness;product=12000;auxiliary=12001;copy_column=obj['constant_copy']
    x=b.lc(obj['cofactor'][3][0]);inv=((q,1),);out=((product,1),)
    raw=[(combine(inv,x,-1),((auxiliary,1),)),(combine(inv,x),combine(((auxiliary,1),),out,4)),
         (combine(out,((copy_column,1),),-1),())]
    if reverse:raw[-1]=(canonical((c,-v) for c,v in raw[-1][0]),())
    rows=rows+raw
    records=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in bb]) for i,(a,bb) in enumerate(rows)]
    header=json.loads(stream.readline());digest=blake3()
    digest.update(relation.NAMESPACE+relation.u64(header['domain_size'])+relation.u64(len(rows))+
                  relation.indices(header['source_public'])+relation.u64(1)+relation.indices(header['source_blocks'][0]))
    for r in records:digest.update(b'A'+relation.terms(r['a'],header['domain_size'])+b'B'+relation.terms(r['b'],header['domain_size']))
    for owner in (obj,caller['metadata']):owner.update(relation_digest=digest.hexdigest(),full_rows=len(rows))
    header.update(relation_digest=digest.hexdigest(),stored_rows=len(rows))
    obj['schema']='shieldd-transfer-asset-nonidentity-v1'
    obj['nonidentity']=dict(asset=obj['asset'],hash=obj['hash'],generator=obj['cofactor'][3],inverse={'source':[1,b.next_witness]})
    obj['expressions'].append(dict(source=[1,b.next_witness],terms=[[q,f'{1:064x}']]))
    b.rho[q]=pow(b.val(obj['cofactor'][3][0]),-1,P);b.rho[product]=1;b.rho[auxiliary]=(b.rho[q]-b.val(obj['cofactor'][3][0]))**2%P
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]))
    return encoded(obj),caller,stream,b,(q,product,auxiliary)


class AssetGeneratorNonidentityTests(unittest.TestCase):
    def test_exact_original_inverse_nonzero_and_constructive_three_writes(self):
        data,caller,stream,b,writes=inverse_fixture()
        extraction=generator.extract(data,stream,caller);cert=generator.certificates(data,extraction,caller)
        self.assertEqual(len(cert['raw']),4)
        plan=generator.completion_plan(data,extraction,caller);self.assertEqual(plan['writes'],list(writes))
        self.assertEqual(len(plan['raw']),3)
        ev=lambda lc:sum(v*b.rho.get(c,0) for c,v in lc)%P
        self.assertTrue(all(ev(a)**2%P==ev(bb) for a,bb in cert['raw'].values()))
        self.assertEqual(ev(cert['checked']['inverse'])*ev(cert['checked']['points'][3][0])%P,1)
        b.rho[writes[0]]=0
        self.assertFalse(all(ev(a)**2%P==ev(bb) for a,bb in cert['raw'].values()))
        _,sound=generator.generate_sound(data,extraction,caller);_,completion=generator.generate_completion(data,extraction,caller)
        self.assertEqual(sound.count('#check @'),3);self.assertEqual(completion.count('#check @'),8)
        self.assertIn('GroupRowCompletion.extend_complete',completion)
        self.assertIn('CompilerSignedCompletion.original_rows',completion)
        self.assertNotIn('(satisfied : Satisfies',completion)
        self.assertIn('def kept : List Nat',completion)
        self.assertNotIn('def kept : List Linear',completion)
        preserved=generator.generate_kept_boundaries(data,extraction,caller)
        self.assertGreater(len(preserved),1)
        for source in preserved.values():
            self.assertEqual(source.count('#check @'),2)
            self.assertIn('freshness_checked',source)
            self.assertNotIn('(satisfied : Satisfies',source)
        for limit in (True,0,255,1025):
            with self.assertRaises(relation.RelationError):
                generator.generate_kept_boundaries(data,extraction,caller,term_limit=limit)
        for i in range(3):
            omitted=copy.deepcopy(extraction)
            row=cert['certificate']['rows'][i]
            omitted['selected_rows']=[r for r in omitted['selected_rows'] if r['row']!=row]
            with self.assertRaises(relation.RelationError):generator.certificates(data,omitted,caller)

    def test_roles_alias_pending_and_reversed_sound_orientation(self):
        data,caller,stream,_,_=inverse_fixture(True)
        extracted=generator.extract(data,stream,caller);_,sound=generator.generate_sound(data,extracted,caller)
        self.assertIn('normalized (by decide)).symm',sound)
        plan=generator.completion_plan(data,extracted,caller)
        _,completed=generator.generate_completion(data,extracted,caller)
        self.assertEqual(len(plan['raw']),3)
        self.assertIn('CompilerSignedCompletion.original_rows',completed)
        self.assertIn('scaleLinear (-1) expected.a',completed)
        obj=json.loads(data)
        for change in ('generator','inverse','pending','extra'):
            altered=copy.deepcopy(obj)
            if change=='generator':altered['nonidentity']['generator']=altered['cofactor'][2]
            elif change=='inverse':altered['nonidentity']['inverse']=altered['values'][3]
            elif change=='pending':altered['repeated_observations_equal']=False
            else:altered['unowned']=True
            with self.assertRaises(relation.RelationError):generator.inspect_metadata(encoded(altered),caller)

    def test_actual_inverse04_negative_assertion_shape(self):
        from pathlib import Path
        from circuits import transfer_arithmetic as arithmetic
        actual=Path(__file__).resolve().parent/'fixtures/asset_generator_inverse_actual_rows.json'
        selected=json.loads(actual.read_bytes())['selected_rows'];copy_column=200692
        raw={r['row']:(canonical((c,int(n,16)) for c,n in r['a']),
                          canonical((c,int(n,16)) for c,n in r['b'])) for r in selected}
        normalized={i:(canonical((0 if c==copy_column else c,n) for c,n in a),
                       canonical((0 if c==copy_column else c,n) for c,n in b)) for i,(a,b) in raw.items()}
        cert=arithmetic.quotient_certificate(((0,1),),((190237,1),),((21198,1),),normalized)
        self.assertIsNone(arithmetic.completion_certificate(cert,normalized))
        assertion=cert['rows'][-1];expected=(combine(cert['output'],cert['numerator'],-1),())
        self.assertEqual(normalized[assertion],(canonical((c,-n) for c,n in expected[0]),()))
        positive=dict(normalized);positive[assertion]=expected
        plan=arithmetic.completion_certificate(cert,positive)
        self.assertEqual([plan[k] for k in ('quotient','product','auxiliary')],[21198,190243,190244])
        rho={0:1,copy_column:1,190237:7,1:83,2:97,21198:23,190243:91,190244:83}
        rho.update({21198:pow(7,-1,P),190243:1,190244:(pow(7,-1,P)-7)**2%P})
        evaluate=lambda terms:sum(rho.get(c,0)*n for c,n in terms)%P
        self.assertTrue(all(evaluate(a)**2%P==evaluate(b) for a,b in raw.values()))
        self.assertEqual([rho[c] for c in (1,2,190237)],[83,97,7])

    def test_complete_map_projection_retains_nonidentity_parent_provenance(self):
        from circuits import transfer_asset_map
        data,caller,_,_,_=inverse_fixture()
        parent=generator.inspect_metadata(data,caller);view=generator.derived_map_view(data,caller)
        self.assertEqual(view['parent_data'],data)
        self.assertEqual(view['parent_schema'],'shieldd-transfer-asset-nonidentity-v1')
        self.assertEqual(view['parent_metadata_sha256'],parent['metadata_sha256'])
        obj=json.loads(view['map_data']);original=json.loads(data)
        self.assertEqual(obj['schema'],'shieldd-transfer-asset-map-v1')
        self.assertNotIn('nonidentity',obj)
        for key in set(obj)-{'schema','expressions'}:self.assertEqual(obj[key],original[key])
        self.assertEqual(len(obj['expressions']),len(original['expressions'])-1)
        accepted=transfer_asset_map.inspect_metadata(view['map_data'],caller)
        for key in ('points','nonlinear','comparisons','asset','hash'):self.assertEqual(accepted[key],parent[key])
        altered=copy.deepcopy(original);altered['ordinary_full_ordered_rows_equal']=False
        with self.assertRaises(relation.RelationError):generator.derived_map_view(encoded(altered),caller)


if __name__=='__main__':unittest.main()
