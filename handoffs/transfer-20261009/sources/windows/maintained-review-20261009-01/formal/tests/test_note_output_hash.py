"""Typed output roles joined to two existing exact source permutations."""
import copy,io,json,tempfile,unittest
from pathlib import Path
from blake3 import blake3
from circuits import transfer_note_output_hash as output_hash,transfer_note_outputs as outputs
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.note_hash_call_fixture import fixture_two_blocks
from tests.test_transfer_note_outputs import fixture as output_fixture
from tests.test_transfer_note_spend import encoded


def fixture(role='note'):
    pages,note,caller,artifact,stream=fixture_two_blocks(domain=15 if role=='note' else 20,arity=8 if role=='note' else 7)
    output_data,_,_,_=output_fixture();out=json.loads(output_data)
    old_pages=[json.loads(data) for data in pages];old_note=json.loads(note)
    observed={tuple(e['source']):tuple((c,int(v,16)) for c,v in e['terms']) for e in out['expressions']}
    old_observed={tuple(e['source']):tuple((c,int(v,16)) for c,v in e['terms']) for e in old_pages[0]['expressions']}
    out['outputs'][0]['note']=old_note['spends'][0]['note']
    if role=='note':out['outputs'][0]['computed_commitment']=old_pages[0]['hash']['output']
    else:out['outputs'][0]['capsule']=old_note['spends'][0]['note'][:7]
    for slot,output in enumerate(out['outputs']):
        for ordinal,bit in enumerate(output['amount_bits']):observed[tuple(bit)]=((600+150*slot+ordinal,1),)
    # Preserve shared source roles; the extra output witnesses are exogenous to
    # this particular captured permutation and occupy disjoint free columns.
    ordinal=0
    shared=set(caller['observed'])|{tuple(ref['source']) for ref in out['outputs'][0]['note']}
    for handle in sorted(observed):
        if handle not in shared and all(handle not in map(tuple,output['amount_bits']) for output in out['outputs']):
            observed[handle]=((900+ordinal,1),);ordinal+=1
    observed.update({h:old_observed[h] for h in shared if h in old_observed})
    computed=tuple(old_pages[0]['hash']['output']['source']);observed[computed]=old_observed[computed]
    # Actual witness handles bind index+3; rename the new exogenous witnesses
    # together with their roles rather than spoofing witness-to-column metadata.
    renamed={h:(1,lc[0][0]-3) for h,lc in observed.items() if h[0]==1 and h not in shared}
    observed={renamed.get(h,h):lc for h,lc in observed.items()}
    for output in out['outputs']:
        refs=[*output['note'],*output['capsule'],*output['payload_key'],output['computed_commitment'],
              output['commitment'],output['capsule_commitment']]
        if output['receiver_inverse'] is not None:refs.append(output['receiver_inverse'])
        for ref in refs:ref['source']=list(renamed.get(tuple(ref['source']),tuple(ref['source'])))
        output['amount_bits']=[list(renamed.get(tuple(bit),tuple(bit))) for bit in output['amount_bits']]
    refs=[]
    for output in out['outputs']:
        refs.extend([*output['note'],*output['capsule'],*output['payload_key'],output['computed_commitment'],
                     output['commitment'],output['capsule_commitment']])
        if output['receiver_inverse'] is not None:refs.append(output['receiver_inverse'])
    required={tuple(ref['source']) for ref in refs}|{tuple(bit) for output in out['outputs'] for bit in output['amount_bits']}
    out['expressions']=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in observed[h]]) for h in sorted(required)]
    supplied_key='commitment' if role=='note' else 'capsule_commitment'
    supplied=observed[tuple(out['outputs'][0][supplied_key]['source'])]
    records=[json.loads(line) for line in stream.getvalue().splitlines()]
    header=records[0];rows=records[1:-1];copy_column=old_pages[0]['constant_copy']
    delta=canonical((copy_column if c==0 else c,v) for c,v in combine(observed[computed],supplied,-1))
    rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in delta],b=[]))
    digest=blake3();domain=header['domain_size']
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+
        relation.indices(header['source_public'])+relation.u64(1)+relation.indices(header['source_blocks'][0]))
    for row in rows:digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    identity=dict(relation_digest=digest.hexdigest(),domain_size=domain,full_rows=len(rows),constant_copy=copy_column)
    header.update(relation_digest=identity['relation_digest'],stored_rows=len(rows));out.update(identity);caller['metadata'].update(identity)
    output_data=encoded(out);new_pages=[]
    for old in old_pages:
        obj={**old,**identity,'schema':'shieldd-transfer-note-output-hash-block-v1','scope':output_hash.SCOPE,'role':role,
             'supplied_commitment':out['outputs'][0][supplied_key]}
        known={tuple(e['source']):tuple((c,int(v,16)) for c,v in e['terms']) for e in old['expressions']}
        known.update(observed)
        needed=set(required)
        for part in old['hash']['blocks']:
            for key in ('before','after'):needed.update(tuple(ref['source']) for ref in part[key] if 'source' in ref)
        for node in old['nodes']:
            for ref in (node['left'],node['right']):
                if ref[0]==0:needed.add(tuple(ref))
            if node['multiply'] and node['left'][0]!=0 and node['right'][0]!=0:
                needed.update(((2,node['index']),tuple(node['left']),tuple(node['right'])))
        obj['expressions']=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in known[h]]) for h in sorted(needed)]
        new_pages.append(encoded(obj))
    return new_pages,output_data,caller,artifact,b''.join(encoded(r) for r in [header,*rows,dict(eof=True,rows=len(rows))])


class NoteOutputHashTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pages,cls.outputs,cls.caller,cls.artifact,cls.rows=fixture()
        cls.directory=tempfile.TemporaryDirectory();cls.root=Path(cls.directory.name)
        (cls.root/'poseidon381-wide.json').write_bytes(encoded(cls.artifact))
    @classmethod
    def tearDownClass(cls):cls.directory.cleanup()

    def test_exact_output_roles_closed_dag_and_all_round_rows(self):
        outputs.inspect_metadata(self.outputs,self.caller)
        for page in self.pages:
            extracted=output_hash.extract(page,io.BytesIO(self.rows),self.outputs,self.caller,self.root)
            selected=output_hash.round_selection(page,extracted,self.outputs,self.caller,self.root)
            self.assertEqual([s['index'] for s in selected['calls'][0]['segments']],list(range(65)))
            self.assertTrue(selected['calls'][0]['role'].startswith('output0.note0.'))
        binding=output_hash.extract_binding(self.pages[1],io.BytesIO(self.rows),self.outputs,self.caller)
        self.assertEqual(len(binding['selected_rows']),2)

    def test_domain_source_absorption_and_row_omission_refuse(self):
        for change in (lambda o:o['hash'].update(domain=20),lambda o:o.update(role='recovery'),
            lambda o:o.update(supplied_commitment=o['hash']['output']),
            lambda o:o['hash']['blocks'][1]['before'].__setitem__(1,o['hash']['inputs'][0])):
            changed=json.loads(self.pages[1]);change(changed)
            with self.assertRaises(relation.RelationError):
                output_hash.inspect_boundaries(encoded(changed),self.outputs,self.caller)
        extracted=output_hash.extract(self.pages[0],io.BytesIO(self.rows),self.outputs,self.caller,self.root)
        changed=copy.deepcopy(extracted);changed['selected_rows'].pop()
        with self.assertRaises(relation.RelationError):
            output_hash.round_selection(self.pages[0],changed,self.outputs,self.caller,self.root)

    def test_recovery20_7_two_blocks_and_distinct_supplied_binding(self):
        pages,outputs_data,caller,artifact,rows=fixture('recovery')
        for page in pages:
            extracted=output_hash.extract(page,io.BytesIO(rows),outputs_data,caller,self.root)
            selected=output_hash.round_selection(page,extracted,outputs_data,caller,self.root)
            self.assertEqual(len(selected['calls'][0]['segments']),65)
            self.assertEqual(selected['calls'][0]['call']['graph']['domain'],20)
            self.assertTrue(selected['calls'][0]['role'].startswith('output0.recovery0.'))
        obj=json.loads(pages[1]);self.assertNotEqual(obj['hash']['output'],obj['supplied_commitment'])
        binding=output_hash.extract_binding(pages[1],io.BytesIO(rows),outputs_data,caller)
        self.assertEqual(len(binding['selected_rows']),2)
        obj['supplied_commitment']=obj['hash']['output']
        with self.assertRaises(relation.RelationError):output_hash.inspect_boundaries(encoded(obj),outputs_data,caller)


if __name__=='__main__':unittest.main()
