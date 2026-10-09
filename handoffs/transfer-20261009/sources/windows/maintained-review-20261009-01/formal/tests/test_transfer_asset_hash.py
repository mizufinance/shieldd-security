"""Exact typed hash/map roots and complete original65-round row extraction."""
import copy,io,json,tempfile,unittest
from pathlib import Path
from circuits import transfer_asset_hash as hashes,transfer_asset_map as maps,poseidon_graph,transfer_relation as relation
from circuits import generate_asset_hash_completion as completion,generate_note_hash_block_completion as blocks
from tests.test_transfer_asset_map import fixture as map_fixture,encoded,P


def fixture():
    params=dict(width=3,ark=[[1+r*3+c for c in range(3)] for r in range(65)],
        mds=[[1+int(r==c) for c in range(3)] for r in range(3)],vectors=[])
    artifact=dict(schema='shieldd.poseidon381.v1',modulus=str(P),alpha=5,full_rounds=8,partial_rounds=57,skip_matrices=0,
        ark=[[f'{n:064x}' for n in row] for row in params['ark']],mds=[[f'{n:064x}' for n in row] for row in params['mds']],vectors=[])
    checkpoint={}
    def build(b,asset):
        before=[dict(native=f'{282:064x}'),asset,dict(native=f'{0:064x}')]
        graph=poseidon_graph.permutation(params,[282,None,0]);refs={}
        for index,node in enumerate(graph['nodes']):
            if node['kind']=='input':ref=asset
            elif node['kind']=='constant':ref=b.constant(node['value'])
            else:ref=(b.mul if node['kind']=='mul' else b.add)(refs[node['left']],refs[node['right']])
            refs[index]=ref
        after=[refs[i] for i in graph['outputs']];checkpoint.update(before=before,after=after)
        return after[1]
    map_data,caller,stream,rows,b=map_fixture(hash_builder=build)
    map_meta=json.loads(map_data);roots={tuple(ref['source']) for ref in checkpoint['before'] if 'source' in ref}
    visited=set();pending=[tuple(ref['source']) for ref in checkpoint['after']]
    while pending:
        ref=pending.pop()
        if ref in visited:continue
        visited.add(ref)
        if ref not in roots and ref[0]==2:pending.extend(tuple(b.nodes[ref[1]][key]) for key in ('left','right'))
    nodes=[node for node in b.nodes if (2,node['index']) in visited and (2,node['index']) not in roots]
    required=roots|{tuple(ref['source']) for ref in checkpoint['after']}|{ref for ref in visited if ref[0]==0}
    for node in nodes:
        if node['multiply'] and node['left'][0]!=0 and node['right'][0]!=0:
            required.update(((2,node['index']),tuple(node['left']),tuple(node['right'])))
    identity={key:map_meta[key] for key in ('relation_digest','domain_size','full_rows','constant_copy')}
    obj=dict(schema='shieldd-transfer-asset-hash-block-v1',family='transfer',scope=hashes.SCOPE,**identity,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=0,role='asset',level=0,block=0,
        map_input=map_meta['values'][0],hash=dict(domain=26,inputs=[map_meta['asset']],output=map_meta['hash'],blocks=[checkpoint]),
        expressions=[dict(source=list(h),terms=[[c,f'{n:064x}'] for c,n in b.expressions[h]]) for h in sorted(required)],nodes=nodes)
    return encoded(obj),map_data,caller,artifact,stream.getvalue(),b,params


class TransferAssetHashTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.page,cls.map,cls.caller,cls.artifact,cls.rows,cls.builder,cls.params=fixture()
        cls.directory=tempfile.TemporaryDirectory();cls.root=Path(cls.directory.name)
        (cls.root/'poseidon381.json').write_bytes(encoded(cls.artifact))
    @classmethod
    def tearDownClass(cls):cls.directory.cleanup()

    def test_real_map_ingress_all65_rounds_and_independent_native_recurrence(self):
        maps.inspect_metadata(self.map,self.caller)
        extracted=hashes.extract(self.page,io.BytesIO(self.rows),self.map,self.caller,self.root)
        selected=hashes.round_selection(self.page,extracted,self.map,self.caller,self.root)
        self.assertEqual([segment['index'] for segment in selected['calls'][0]['segments']],list(range(65)))
        self.assertEqual(selected['calls'][0]['parameters']['width'],3)
        state=[282,17,0]
        for index,segment in enumerate(selected['calls'][0]['segments']):
            shifted=[(state[lane]+self.params['ark'][index][lane])%P for lane in range(3)]
            powered=[pow(n,5,P) if index<4 or index>=61 or lane==0 else n for lane,n in enumerate(shifted)]
            state=[sum(coefficient*value for coefficient,value in zip(row,powered))%P for row in self.params['mds']]
            for terms,expected in zip(segment['after'],state):
                self.assertEqual(sum(self.builder.rho.get(c,0)*v for c,v in terms)%P,expected)
        self.assertEqual(self.builder.val(json.loads(self.map)['hash']),state[1])
        modules=hashes.generate_permutation(self.page,extracted,self.map,self.caller,self.root)
        self.assertEqual(len(modules),15)
        self.assertTrue(any('Poseidon.State Linear 3' in source for _,source in modules))
        self.assertEqual(sum(source.count('#print axioms') for _,source in modules),133)

    def test_domain_asset_u_iv_width_source_and_semantic_row_changes_refuse(self):
        for change in (lambda o:o['hash'].update(domain=25),lambda o:o['hash'].update(inputs=[o['hash']['output']]),
            lambda o:o.update(map_input=o['hash']['inputs'][0]),lambda o:o['hash']['blocks'][0]['before'].__setitem__(0,dict(native=f'{281:064x}')),
            lambda o:o['hash']['blocks'][0]['after'].pop(),lambda o:o.update(ordinary_full_ordered_rows_equal=False)):
            obj=json.loads(self.page);change(obj)
            with self.assertRaises(relation.RelationError):hashes.inspect_boundaries(encoded(obj),self.map,self.caller)
        extracted=hashes.extract(self.page,io.BytesIO(self.rows),self.map,self.caller,self.root)
        changed=copy.deepcopy(extracted);changed['selected_rows'].pop()
        with self.assertRaises(relation.RelationError):hashes.round_selection(self.page,changed,self.map,self.caller,self.root)
        obj=json.loads(self.page);obj['nodes'][20]['multiply']=not obj['nodes'][20]['multiply']
        with self.assertRaises(relation.RelationError):hashes.inspect_metadata(encoded(obj),self.map,self.caller,self.root)

    def test_hash_constructor_owns_only_materializations_and_closes_hash3_native_value(self):
        extracted=hashes.extract(self.page,io.BytesIO(self.rows),self.map,self.caller,self.root)
        selected=hashes.round_selection(self.page,extracted,self.map,self.caller,self.root)
        checked=hashes.inspect_metadata(self.page,self.map,self.caller,self.root)
        context=selected,checked,dict(metadata={},readonly_lcs=list(self.caller['observed'].values()))
        rho={c:(37*c+9)%P for c in range(32768)};rho[0]=rho[32000]=1;original=dict(rho)
        owned=set();actual={};state=[282,rho[3],0];evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%P
        for start in range(0,65,5):
            plan=blocks._chunk_plan(context,start,min(start+5,65))
            for step in plan['steps']:
                left=evaluate(step['left']);remainder=evaluate(step['remainder'])
                if step['kind']=='square':value=left*left
                else:
                    right=evaluate(step['right']);value=left*right;rho[step['auxiliary']]=(left-right)**2%P
                rho[step['output']]=(value-remainder)%P
            for index in range(start,min(start+5,65)):
                shifted=[(state[c]+self.params['ark'][index][c])%P for c in range(3)]
                powered=[pow(n,5,P) if index<4 or index>=61 or c==0 else n for c,n in enumerate(shifted)]
                state=[sum(coefficient*n for coefficient,n in zip(row,powered))%P for row in self.params['mds']]
            self.assertEqual([evaluate(lc) for lc in selected['calls'][0]['segments'][min(start+4,64)]['after']],state)
            owned.update(plan['writes']);actual.update(plan['raw'])
        self.assertTrue(all(evaluate(a)**2%P==evaluate(z) for a,z in actual.values()))
        self.assertTrue(all(rho[c]==original[c] for c in original if c not in owned))
        modules=list(completion.generate(self.page,extracted,self.map,self.caller,self.root))
        self.assertEqual(len(modules),30);self.assertEqual(sum(source.count('#print axioms') for _,source in modules),272)
        final=modules[-1][1];signature=final[final.index('theorem complete_hash'):final.index(' := by',final.index('theorem complete_hash'))]
        self.assertIn('Poseidon.hash3',signature);self.assertNotIn('(satisfied :',signature)
        self.assertNotIn('RuntimeHashBlock_spend',final)
        self.assertIn('RuntimeHashBlock_balance0_asset0_permutation0_0.rawRoundRows',final)
        self.assertIn('RuntimeHashBlock_balance0_asset0_permutation0_0.parameters',signature)
        renamed=list(completion.generate(self.page,extracted,self.map,self.caller,self.root,base='RuntimeTransferActualAssetHash'))
        self.assertEqual(len(renamed),30)
        self.assertTrue(all(name.startswith('RuntimeTransferActualAssetHash') for name,_ in renamed))
        self.assertIn('RuntimeTransferActualAssetHash.actual_hash_sound',renamed[-1][1])
        chunks=[f'RuntimeTransferAssetHashCompletionChunk{i}' for i in range(13)]
        obj=checked['metadata']
        legacy=blocks._composition('RuntimeTransferAssetHash',chunks,obj)
        explicit=blocks._composition('RuntimeTransferAssetHash',chunks,obj,
            permutation_namespace='RuntimeHashBlock_spend0_asset0_permutation0_0')
        self.assertEqual(legacy,explicit)
        with self.assertRaises(relation.RelationError):
            list(completion.generate(self.page,extracted,self.map,self.caller,self.root,base='broken\nimport'))
        rho[max(owned)]=(rho[max(owned)]+1)%P
        self.assertFalse(all(evaluate(a)**2%P==evaluate(z) for a,z in actual.values()))


if __name__=='__main__':unittest.main()
