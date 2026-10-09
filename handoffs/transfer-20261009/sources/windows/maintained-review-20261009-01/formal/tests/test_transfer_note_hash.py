"""Synthetic ordinary-row/source-cone controls, no runtime qualification."""
import copy,io,json,tempfile,unittest
from pathlib import Path
from blake3 import blake3
from circuits import transfer_note_hash as h,transfer_note_spend as notes,transfer_relation as relation,poseidon_graph
from circuits.transfer_balance_rows import canonical,combine
from circuits.generate_hash_round import generate_selected_round
from tests.test_transfer_note_spend import fixture,encoded


def hash_fixture():
    note_data,_,caller=fixture();note=json.loads(note_data);accepted=notes.inspect_metadata(note_data,caller)
    observed=dict(accepted['observed']);spend=note['spends'][0]
    inputs=[{'native':f'{1:064x}'},spend['note'][0],spend['note'][1],spend['note'][2],spend['position']]
    before=[{'native':f'{1281:064x}'},*inputs]
    params=dict(width=6,ark=[[1+r*6+c for c in range(6)] for r in range(65)],mds=[[1+int(r==c) for c in range(6)] for r in range(6)],vectors=[])
    artifact=dict(schema='shieldd.poseidon381.v1',modulus=str(h.P),alpha=5,full_rounds=8,partial_rounds=57,
        skip_matrices=0,ark=[[f'{v:064x}' for v in row] for row in params['ark']],mds=[[f'{v:064x}' for v in row] for row in params['mds']],vectors=[])
    graph=poseidon_graph.permutation(params,[1281,1,None,None,None,None]);refs={};derived={};nodes={};rows=[];next_column=1001
    outline=lambda lc:canonical((1000 if c==0 else c,v) for c,v in lc)
    for index,node in enumerate(graph['nodes']):
        if node['kind']=='input':
            ref=inputs[1+node['slot']]['source'];lc=observed[tuple(ref)]
        elif node['kind']=='constant':ref=[0,10000+index];lc=canonical([(0,node['value'])])
        else:
            ref=[2,10000+index];left,right=refs[node['left']],refs[node['right']];a,b=derived[node['left']],derived[node['right']]
            nodes[tuple(ref)]=dict(index=ref[1],multiply=node['kind']=='mul',left=left,right=right)
            if node['kind']=='add':lc=combine(a,b)
            elif all(c==0 for c,_ in a):lc=canonical((c,v*(a[0][1] if a else 0)) for c,v in b)
            else:
                lc=((next_column,1),);next_column+=1
                if a==b:rows.append((outline(a),lc))
                else:
                    auxiliary=((next_column,1),);next_column+=1
                    rows.extend([(outline(combine(a,b,-1)),auxiliary),(outline(combine(a,b)),combine(auxiliary,lc,4))])
        refs[index]=ref;derived[index]=lc
    after=[{'source':refs[i]} for i in graph['outputs']]
    boundaries={tuple(ref['source']) for ref in before if 'source' in ref};visited=set();pending=[tuple(ref['source']) for ref in after]
    while pending:
        ref=pending.pop()
        if ref in visited:continue
        visited.add(ref)
        if ref in boundaries:continue
        if ref in nodes:pending.extend(tuple(nodes[ref][k]) for k in ('left','right'))
    table={ref:node for ref,node in nodes.items() if ref in visited}
    needed=set(observed)|{ref for ref in visited if ref[0]==0}|{tuple(ref['source']) for ref in after}
    for ref,node in table.items():
        if node['multiply'] and node['left'][0]!=0 and node['right'][0]!=0:
            needed.update((ref,tuple(node['left']),tuple(node['right'])))
    for index,ref in refs.items():
        if tuple(ref) in needed:observed[tuple(ref)]=derived[index]
    rows=[(canonical([(0,1),(1000,-1)]),()),*rows]
    records=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]) for i,(a,b) in enumerate(rows)]
    digest=blake3();public=[[1,990]];blocks=[[1,991]];domain=2048
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+relation.indices(public)+relation.u64(1)+relation.indices(blocks))
    for row in records:digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    identity=dict(relation_digest=digest.hexdigest(),domain_size=domain,full_rows=len(rows),constant_copy=1000)
    note.update(identity);caller['metadata'].update(identity)
    obj=dict(schema='shieldd-transfer-note-hash-block-v1',family='transfer',scope=h.SCOPE,**identity,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=0,role='state',level=0,block=0,
        hash=dict(domain=1,inputs=inputs,output=after[1],blocks=[dict(before=before,after=after)]),
        expressions=[dict(source=list(ref),terms=[[c,f'{v:064x}'] for c,v in lc]) for ref,lc in sorted(observed.items())],
        nodes=sorted(table.values(),key=lambda node:node['index']))
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity['relation_digest'],domain_size=domain,
        stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,public_columns=[1],committed_columns=[[2]],
        source_public=public,source_blocks=[blocks],coefficient_encoding='canonical-big-endian-32',field_modulus=str(h.P),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',padding='implicit-all-zero-rows-to-domain-size')
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]))
    return obj,encoded(note),caller,artifact,stream


def boundary_fixture(role,slot=0,block=0):
    data,_,caller=fixture();accepted=notes.inspect_metadata(data,caller);note=accepted['metadata'];spend=note['spends'][slot]
    observed=dict(accepted['observed'])
    def fresh(index,lc=None):
        observed[(2,index)]=lc if lc is not None else ((100+index-5000,1),)
        return dict(source=[2,index])
    if role=='commitment':domain,inputs,output=15,spend['note'],spend['commitment']
    elif role=='nullifier':domain,inputs,output=7,[spend['shared']['nk'],spend['commitment'],spend['position']],spend['real_nullifier']
    else:domain,inputs,output=22,[spend['optional']['seed'],spend['shared']['randomizer'],dict(native=f'{1:064x}')],spend['optional']['synthetic']
    def lc(ref):return observed[tuple(ref['source'])] if 'source' in ref else canonical([(0,int(ref['native'],16))])
    before=[dict(native=f'{256*len(inputs)+domain:064x}'),*inputs[:5]]
    before.extend(dict(native=f'{0:064x}') for _ in range(6-len(before)))
    after=[fresh(5000+i) for i in range(6)]
    blocks=[dict(before=before,after=after)]
    if role=='commitment':
        before=[after[0]]+[fresh(5010+i,combine(lc(after[1+i]),lc(inputs[5+i]))) for i in range(3)]+after[4:]
        after=[fresh(5020+i) for i in range(6)]
        blocks.append(dict(before=before,after=after))
    blocks[-1]['after'][1]=output
    obj=dict(schema='shieldd-transfer-note-hash-block-v1',family='transfer',scope=h.SCOPE,
        **{k:note[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')},
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=slot,role=role,level=0,block=block,
        hash=dict(domain=domain,inputs=inputs,output=output,blocks=blocks),nodes=[],
        expressions=[dict(source=list(ref),terms=[[c,f'{v:064x}'] for c,v in terms]) for ref,terms in sorted(observed.items())])
    return obj,data,caller


class NoteHashTests(unittest.TestCase):
    def setUp(self):
        self.obj,self.note,self.caller,self.artifact,self.stream=hash_fixture()
        self.directory=tempfile.TemporaryDirectory();self.root=Path(self.directory.name)
        (self.root/'poseidon381-wide.json').write_text(json.dumps(self.artifact))
    def tearDown(self):self.directory.cleanup()
    def checked(self,obj=None):return h.inspect_metadata(encoded(obj or self.obj),self.note,self.caller,self.root)

    def test_complete_native_recipe_cone_actual_rows_and_round_generator(self):
        state=self.checked();self.assertEqual(len(state['graph']['segments']),65)
        selected=h.extract(encoded(self.obj),self.stream,self.note,self.caller,self.root)
        adapted=h.round_selection(encoded(self.obj),json.loads(json.dumps(selected)),self.note,self.caller,self.root)
        self.assertEqual(len(adapted['calls'][0]['segments']),65)
        text=generate_selected_round(self.obj,adapted,adapted['calls'][0]['role'],0,0,state['metadata_sha256'])
        self.assertEqual(text.count('#print axioms'),2)
        self.assertIn('Poseidon.RoundCertificate',text)
        self.assertNotIn('sorry',text)

    def test_pending_role_capacity_and_shared_note_refusals(self):
        cases=[('parity',lambda o:o.update(repeated_observations_equal=False)),
               ('role',lambda o:o.update(role='dummy')),
               ('absorbed',lambda o:o['hash']['blocks'][0]['before'][0].update(native=f'{1282:064x}')),
               ('two-note',lambda o:o['expressions'].pop())]
        for reason,change in cases:
            obj=copy.deepcopy(self.obj);change(obj)
            with self.subTest(reason=reason),self.assertRaises(relation.RelationError):self.checked(obj)

    def test_all_lane_source_missing_node_and_row_semantic_refusals(self):
        changed=copy.deepcopy(self.obj);changed['nodes'].pop()
        with self.assertRaisesRegex(relation.RelationError,'missing source node'):self.checked(changed)
        changed=copy.deepcopy(self.obj);changed['hash']['blocks'][0]['after'][0]=changed['hash']['blocks'][0]['after'][1]
        with self.assertRaises(relation.RelationError):self.checked(changed)
        selected=h.extract(encoded(self.obj),self.stream,self.note,self.caller,self.root)
        changed=copy.deepcopy(selected);changed['selected_rows'].pop()
        with self.assertRaisesRegex(relation.RelationError,'missing'):
            h.round_selection(encoded(self.obj),changed,self.note,self.caller,self.root)

    def test_note_nullifier_and_dummy_native_source_roles_and_capacity(self):
        for role,slot,block in [('commitment',0,0),('commitment',0,1),('commitment',1,0),('commitment',1,1),
                                ('nullifier',0,0),('nullifier',1,0),('dummy',1,0)]:
            obj,note,caller=boundary_fixture(role,slot,block)
            with self.subTest(role=role,slot=slot,block=block):
                h.inspect_boundaries(encoded(obj),note,caller)
                changed=copy.deepcopy(obj);changed['hash']['domain']+=1
                with self.assertRaisesRegex(relation.RelationError,'domain/arity'):h.inspect_boundaries(encoded(changed),note,caller)
                changed=copy.deepcopy(obj);changed['hash']['inputs'][0]=changed['hash']['inputs'][1]
                with self.assertRaisesRegex(relation.RelationError,'source role'):h.inspect_boundaries(encoded(changed),note,caller)
        obj,note,caller=boundary_fixture('commitment',0,1)
        obj['hash']['blocks'][1]['before'][5]=obj['hash']['blocks'][0]['after'][4]
        with self.assertRaisesRegex(relation.RelationError,'absorbed'):h.inspect_boundaries(encoded(obj),note,caller)


if __name__=='__main__':unittest.main()
