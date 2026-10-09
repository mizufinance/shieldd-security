"""Closed two-permutation source/ordinary-row fixture; never runtime evidence."""
import io,json
from blake3 import blake3
from circuits import poseidon_graph,transfer_note_spend as notes,transfer_note_hash as hashes
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_note_spend import fixture,encoded


def fixture_two_blocks(slot=0,*,domain=15,arity=8):
    hash_domain=domain
    note_data,_,caller=fixture();note=json.loads(note_data)
    observed=dict(notes.inspect_metadata(note_data,caller)['observed']);spend=note['spends'][slot]
    params=dict(width=6,ark=[[1+r*6+c for c in range(6)] for r in range(65)],
                mds=[[1+int(r==c) for c in range(6)] for r in range(6)],vectors=[])
    artifact=dict(schema='shieldd.poseidon381.v1',modulus=str(relation.MODULUS),alpha=5,full_rounds=8,
        partial_rounds=57,skip_matrices=0,ark=[[f'{v:064x}' for v in row] for row in params['ark']],
        mds=[[f'{v:064x}' for v in row] for row in params['mds']],vectors=[])
    copy=4000;next_column=1100;rows=[];blocks=[];tables=[];all_values=dict(observed)
    def value(ref):return all_values[tuple(ref['source'])] if 'source' in ref else canonical([(0,int(ref['native'],16))])
    if domain not in (15,20) or arity not in (7,8):raise ValueError('two-block fixture role budget')
    before=[dict(native=f'{256*arity+domain:064x}'),*spend['note'][:5]]
    for block in range(2):
        graph=poseidon_graph.permutation(params,[int(ref['native'],16) if 'native' in ref else None for ref in before])
        inputs=[ref for ref in before if 'source' in ref];refs={};derived={};nodes={}
        for index,node in enumerate(graph['nodes']):
            if node['kind']=='input':ref=inputs[node['slot']]['source'];lc=value(inputs[node['slot']])
            elif node['kind']=='constant':ref=[0,10000+block*20000+index];lc=canonical([(0,node['value'])])
            else:
                ref=[2,10000+block*20000+index];left,right=refs[node['left']],refs[node['right']]
                a,b=derived[node['left']],derived[node['right']]
                nodes[tuple(ref)]=dict(index=ref[1],multiply=node['kind']=='mul',left=left,right=right)
                if node['kind']=='add':lc=combine(a,b)
                elif all(c==0 for c,_ in a):lc=canonical((c,v*(a[0][1] if a else 0)) for c,v in b)
                else:
                    lc=((next_column,1),);next_column+=1
                    if a==b:rows.append((a,lc))
                    else:
                        auxiliary=((next_column,1),);next_column+=1
                        rows.extend([(combine(a,b,-1),auxiliary),(combine(a,b),combine(auxiliary,lc,4))])
            refs[index]=ref;derived[index]=lc;all_values[tuple(ref)]=lc
        after=[dict(source=refs[i]) for i in graph['outputs']]
        tables.append(nodes);blocks.append(dict(before=before,after=after))
        if block==0:
            before=[after[0]]
            for lane in range(1,6):
                if lane<=arity-5:
                    ref=dict(source=[2,28000+lane]);all_values[tuple(ref['source'])]=combine(value(after[lane]),value(spend['note'][4+lane]))
                    before.append(ref)
                else:before.append(after[lane])
    old_commitment=tuple(spend['commitment']['source']);spend['commitment']=blocks[-1]['after'][1]
    del observed[old_commitment];observed[tuple(spend['commitment']['source'])]=value(spend['commitment'])
    note['expressions']=[dict(source=list(ref),terms=[[c,f'{v:064x}'] for c,v in lc]) for ref,lc in sorted(observed.items())]
    outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    rows=[(canonical([(0,1),(copy,-1)]),()),*[(outline(a),outline(b)) for a,b in rows]]
    records=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]) for i,(a,b) in enumerate(rows)]
    digest=blake3();public=[[1,990]];committed=[[1,991]];domain=4096
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+relation.indices(public)+relation.u64(1)+relation.indices(committed))
    for row in records:digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    identity=dict(relation_digest=digest.hexdigest(),domain_size=domain,full_rows=len(rows),constant_copy=copy)
    note.update(identity);caller['metadata'].update(identity);note_data=encoded(note)
    call=dict(domain=hash_domain,inputs=spend['note'][:arity],output=spend['commitment'],blocks=blocks)
    pages=[]
    for block,table in enumerate(tables):
        base=dict(schema='shieldd-transfer-note-hash-block-v1',family='transfer',scope=hashes.SCOPE,**identity,
            ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=slot,role='commitment',level=0,
            block=block,hash=call,nodes=[],expressions=[])
        # Boundary coverage includes both permutations, but the source DAG is
        # closed only over this page's six outputs and six initial coordinates.
        boundary={tuple(r['source']) for part in blocks for k in ('before','after') for r in part[k] if 'source' in r}
        boundary.update(tuple(r['source']) for r in call['inputs']);boundary.add(tuple(call['output']['source']))
        current_inputs={tuple(r['source']) for r in blocks[block]['before'] if 'source' in r}
        visited=set();pending=[tuple(r['source']) for r in blocks[block]['after']]
        while pending:
            ref=pending.pop()
            if ref in visited:continue
            visited.add(ref)
            if ref not in current_inputs and ref in table:pending.extend(tuple(table[ref][k]) for k in ('left','right'))
        chosen={ref:node for ref,node in table.items() if ref in visited}
        required=set(observed)|boundary|{ref for ref in visited if ref[0]==0}
        for ref,node in chosen.items():
            if node['multiply'] and node['left'][0]!=0 and node['right'][0]!=0:
                required.update((ref,tuple(node['left']),tuple(node['right'])))
        base['nodes']=sorted(chosen.values(),key=lambda n:n['index'])
        base['expressions']=[dict(source=list(ref),terms=[[c,f'{v:064x}'] for c,v in all_values[ref]]) for ref in sorted(required)]
        pages.append(encoded(base))
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity['relation_digest'],domain_size=domain,
        stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,public_columns=[1],committed_columns=[[2]],
        source_public=public,source_blocks=[committed],coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',padding='implicit-all-zero-rows-to-domain-size')
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]))
    return pages,note_data,caller,artifact,stream
