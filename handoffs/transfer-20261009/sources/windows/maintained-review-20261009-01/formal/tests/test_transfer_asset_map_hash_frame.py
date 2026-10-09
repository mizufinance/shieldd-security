"""Independent tiny combined hash/map/inverse row fixture and source fences."""
import copy,io,json,re,tempfile,unittest
from pathlib import Path
from blake3 import blake3
from circuits import transfer_asset_map_hash_frame as frame
from circuits import transfer_asset_map_completion as completion
from circuits import transfer_asset_map as maps, transfer_asset_hash as hashes
from circuits import transfer_asset_generator_nonidentity as inverse, transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_asset_hash import fixture as hash_fixture, encoded
from tests.test_asset_asserted_squares import defer_captured
from tests.test_transfer_asset_map import square_root


def fixture():
    page,map_data,caller,artifact,raw,b,parameters=hash_fixture()
    obj=json.loads(map_data);records=[json.loads(line) for line in raw.splitlines()]
    q=3+b.next_witness;product=b.next_column;auxiliary=product+1
    x=b.lc(obj['cofactor'][3][0]);copy_column=obj['constant_copy']
    extra=[(combine(((q,1),),x,-1),((auxiliary,1),)),
           (combine(((q,1),),x),((product,4),(auxiliary,1))),
           (combine(((copy_column,1),),((product,1),),-1),())]
    for a,bb in extra:
        records.insert(-1,dict(row=len(records)-2,a=[[c,f'{n:064x}'] for c,n in canonical(a)],
            b=[[c,f'{n:064x}'] for c,n in canonical(bb)]))
    digest=blake3();header=records[0];domain=header['domain_size'];count=len(records)-2
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(count)+relation.indices(header['source_public'])+
        relation.u64(1)+relation.indices(header['source_blocks'][0]))
    for row in records[1:-1]:digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    obj.update(schema='shieldd-transfer-asset-nonidentity-v1',relation_digest=digest.hexdigest(),full_rows=count)
    obj['nonidentity']=dict(asset=obj['asset'],hash=obj['hash'],generator=obj['cofactor'][3],inverse={'source':[1,b.next_witness]})
    obj['expressions'].append(dict(source=[1,b.next_witness],terms=[[q,f'{1:064x}']]))
    caller=copy.deepcopy(caller);caller['metadata'].update(relation_digest=digest.hexdigest(),full_rows=count)
    header.update(relation_digest=digest.hexdigest(),stored_rows=count);records[-1].update(rows=count)
    parent,caller,raw,b=defer_captured(encoded(obj),caller,b''.join(encoded(row) for row in records),b)
    parent_obj=json.loads(parent);page_obj=json.loads(page)
    for key in ('relation_digest','domain_size','full_rows','constant_copy'):page_obj[key]=parent_obj[key]
    return encoded(page_obj),parent,caller,artifact,raw,b,parameters


class AssetHashFrameTests(unittest.TestCase):
    def test_dual_fence_reuses_exact_hash_chunks_and_derives_entire_cone(self):
        page,parent,caller,artifact,raw,b,_=fixture()
        map_data=inverse.derived_map_view(parent,caller)['map_data']
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);(root/'poseidon381.json').write_bytes(encoded(artifact))
            selected=hashes.extract(page,io.BytesIO(raw),map_data,caller,root)
            mapped=maps.extract(map_data,io.BytesIO(raw),caller)
            admitted=inverse.extract(parent,io.BytesIO(raw),caller)
            recipe=frame.plan(page,selected,map_data,mapped,parent,admitted,caller,root)
            self.assertEqual(len(recipe['chunks']),13)
            self.assertLessEqual(recipe['upper'],recipe['floor'])
            self.assertEqual(set().union(*(set(c['raw']) for c in recipe['chunks'])),set(recipe['join']['selected']['rows']))
            writes=set(recipe['map']['map']['recipe']['owned_writes'])|set(recipe['map']['writes'])
            for chunk in recipe['chunks']:
                for a,bb in chunk['raw'].values():
                    self.assertTrue(set(c for c,_ in a+bb).isdisjoint(writes))
            # Construct the entire cone from arbitrary owned witnesses. Check
            # final original rows independently, after all later writes.
            rho=dict(b.rho);rho[0]=rho[recipe['copy']]=1;rho[1]=83;rho[2]=97
            original=dict(rho)
            hash_writes={column for chunk in recipe['chunks'] for column in chunk['writes']}
            for column in writes|hash_writes:rho[column]=(37*column+19)%maps.P
            evaluate=lambda terms:sum(rho.get(c,0)*n for c,n in terms)%maps.P
            for chunk in recipe['chunks']:
                for step in chunk['steps']:
                    left=evaluate(step['left']);remainder=evaluate(step['remainder'])
                    if step['kind']=='square':value=left*left
                    else:
                        right=evaluate(step['right']);value=left*right
                        rho[step['auxiliary']]=(left-right)**2%maps.P
                    rho[step['output']]=(value-remainder)%maps.P
            rho=completion.construct(map_data,mapped,caller,rho,square_root)['assignment']
            x=evaluate(recipe['map']['inverse']['denominator'])
            self.assertNotEqual(x,0) # This positive fixture passes native identity admission.
            q,product,auxiliary=recipe['map']['writes']
            rho[q]=pow(x,-1,maps.P);rho[product]=1;rho[auxiliary]=(rho[q]-x)**2%maps.P
            for chunk in recipe['chunks']:
                for a,bb in chunk['raw'].values():self.assertEqual(evaluate(a)**2%maps.P,evaluate(bb))
            for a,bb in recipe['map']['map']['recipe']['raw'].values():
                self.assertEqual(evaluate(a)**2%maps.P,evaluate(bb))
            for a,bb in recipe['map']['inverse']['raw'].values():
                self.assertEqual(evaluate(a)**2%maps.P,evaluate(bb))
            self.assertEqual([rho[1],rho[2]],[83,97])
            self.assertTrue(all(rho[column]==value for column,value in original.items()
                                if column not in writes|hash_writes))
            name,source=frame.generate(page,selected,map_data,mapped,parent,admitted,caller,root)
            self.assertEqual(name,'RuntimeTransferAssetConeCompletion')
            checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
            self.assertEqual(len(checks),18);self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
            self.assertEqual(source.count('theorem support'),13)
            self.assertNotIn('def rawChunks',source)
            self.assertNotIn('255).all',source)
            self.assertIn('NumericConstruction.writes_checked',source)
            self.assertIn('HashJoin.complete_map_inverse',source)
            self.assertIn('theorem preserves ',source)
            self.assertIn('HashCompletionChunk12.rawRows',source)
            statement=source[source.index('theorem complete_rows'):].split(':= by',1)[0]
            for forbidden in ('(satisfied','(nonidentity','(nativeInput','(legal'):
                self.assertNotIn(forbidden,statement)


if __name__=='__main__':unittest.main()
