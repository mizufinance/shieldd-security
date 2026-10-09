"""Native recovery domain/arity, counter, source and absorption controls."""
import copy,io,json,tempfile,unittest
from pathlib import Path
from circuits import transfer_recovery_hash as hashes,transfer_relation as relation
from circuits import generate_recovery_hash_completion as completion,generate_note_hash_block_completion as blocks
from tests.test_transfer_recovery_capsule import fixture
from tests.test_transfer_note_spend import encoded


def pages():
    recovery,output,caller,_=fixture();meta=json.loads(recovery)
    for slot,entry in enumerate(meta['capsules']):
        for role in hashes.ROLES:
            if role=='secret':domain,width,inputs,result=11,3,entry['shared'],entry['secret']
            elif role=='confirmation':domain,width,inputs,result=21,6,[entry['seed'],*entry['capsule'][:2],entry['capsule'][3]],entry['computed_confirmation']
            else:
                counter=int(role=='blinding-stream');domain,width=10,3
                inputs=[entry['seed'],{'native':f'{counter:064x}'}];result=entry['blinding_stream' if counter else 'amount_stream']
            before=[{'native':f'{domain+256*len(inputs):064x}'},*inputs]
            before.extend([{'native':f'{0:064x}'}]*(width-len(before)))
            after=[entry['computed_epk'][0],result,*entry['shared']]
            after=(after+[entry['amount_stream'],entry['blinding_stream']])[:width]
            obj=dict(schema='shieldd-transfer-recovery-hash-block-v1',family='transfer',scope=hashes.SCOPE,
                **{k:meta[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')},
                ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=slot,role=role,level=0,block=0,
                hash=dict(domain=domain,inputs=inputs,output=result,blocks=[dict(before=before,after=after)]),
                expressions=meta['expressions'],nodes=[])
            yield obj,recovery,output,caller,width


class RecoveryHashTests(unittest.TestCase):
    def test_closed_source_cones_construct_all_rows_and_match_independent_native_hash(self):
        from tests.recovery_hash_fixture import fixture as cone_fixture
        for role in ('secret','confirmation','blinding-stream'):
            page,recovery,output,caller,artifact,rows,builder,params=cone_fixture(role)
            width=params['width'];p=relation.MODULUS
            with tempfile.TemporaryDirectory() as directory:
                root=Path(directory);(root/('poseidon381.json' if width==3 else 'poseidon381-wide.json')).write_bytes(encoded(artifact))
                extracted=hashes.extract(page,io.BytesIO(rows),recovery,output,caller,root)
                selected=hashes.round_selection(page,extracted,recovery,output,caller,root)
                checked=hashes.inspect_metadata(page,recovery,output,caller,root)
                context=selected,checked,dict(metadata={},readonly_lcs=list(caller['observed'].values()))
                rho={c:(37*c+29)%p for c in range(32768)};rho[0]=rho[32000]=1;original=dict(rho);owned=set();actual={}
                evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%p
                state=[evaluate(lc) for lc in selected['calls'][0]['segments'][0]['before']]
                for start in range(0,65,5):
                    plan=blocks._chunk_plan(context,start,min(start+5,65))
                    for step in plan['steps']:
                        left=evaluate(step['left']);value=left*left
                        if step['kind']!='square':
                            right=evaluate(step['right']);value=left*right;rho[step['auxiliary']]=(left-right)**2%p
                        rho[step['output']]=(value-evaluate(step['remainder']))%p
                    for index in range(start,min(start+5,65)):
                        shifted=[(state[lane]+params['ark'][index][lane])%p for lane in range(width)]
                        powered=[pow(n,5,p) if index<4 or index>=61 or lane==0 else n for lane,n in enumerate(shifted)]
                        state=[sum(c*n for c,n in zip(row,powered))%p for row in params['mds']]
                    self.assertEqual([evaluate(lc) for lc in selected['calls'][0]['segments'][min(start+4,64)]['after']],state)
                    actual.update(plan['raw']);owned.update(plan['writes'])
                self.assertTrue(all(evaluate(a)**2%p==evaluate(z) for a,z in actual.values()))
                self.assertTrue(all(rho[c]==original[c] for c in rho if c not in owned))
                modules=list(completion.generate(page,extracted,recovery,output,caller,root))
                self.assertEqual(len(modules),30)
                self.assertEqual(sum(source.count('#print axioms') for _,source in modules),272)
                final=modules[-1][1];signature=final[final.index('theorem complete_hash'):final.index(' := by',final.index('theorem complete_hash'))]
                self.assertIn('Poseidon.hash3' if width==3 else 'Poseidon.hash',signature)
                self.assertNotIn('(satisfied :',signature)
                bad=copy.deepcopy(extracted);bad['selected_rows'].pop()
                with self.assertRaises(relation.RelationError):hashes.round_selection(page,bad,recovery,output,caller,root)
                modified=json.loads(page);modified['nodes'][20]['multiply']=not modified['nodes'][20]['multiply']
                with self.assertRaises(relation.RelationError):hashes.inspect_metadata(encoded(modified),recovery,output,caller,root)

    def test_eight_exact_native_call_boundaries_and_both_widths(self):
        count=0
        for obj,recovery,output,caller,width in pages():
            checked=hashes.inspect_boundaries(encoded(obj),recovery,output,caller)
            self.assertEqual(checked['width'],width);count+=1
        self.assertEqual(count,8)

    def test_native_counter_domain_source_absorption_and_pending_controls(self):
        for obj,recovery,output,caller,_ in pages():
            mutations=[lambda o:o.update(repeated_observations_equal=False),lambda o:o.update(block=1),
                lambda o:o['hash'].update(domain=o['hash']['domain']+1),lambda o:o['hash']['inputs'].reverse(),
                lambda o:o['hash'].update(output=o['hash']['blocks'][0]['after'][0]),
                lambda o:o['hash']['blocks'][0]['before'].__setitem__(0,{'native':f'{0:064x}'}),
                lambda o:o['expressions'].pop()]
            for mutate in mutations:
                changed=copy.deepcopy(obj);mutate(changed)
                with self.assertRaises(relation.RelationError):hashes.inspect_boundaries(encoded(changed),recovery,output,caller)
            if obj['role'].endswith('stream'):
                changed=copy.deepcopy(obj);changed['hash']['inputs'][1]={'native':f'{2:064x}'}
                with self.assertRaisesRegex(relation.RelationError,'native domain'):hashes.inspect_boundaries(encoded(changed),recovery,output,caller)


if __name__=='__main__':unittest.main()
