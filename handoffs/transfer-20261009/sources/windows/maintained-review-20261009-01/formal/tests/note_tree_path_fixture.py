"""Synthetic24 closed state cones with physically interleaved owned writes.

Pages are serialized one at a time. These synthetic rows exercise source/row
transport and construction; their identity flags are never runtime evidence.
"""
import hashlib,io,json
from pathlib import Path
from blake3 import blake3
from circuits import transfer_relation as relation,transfer_note_tree as tree,transfer_note_hash as hashes,poseidon_graph
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_note_spend import fixture,encoded,source


def path_fixture(directory):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    note_data,_,caller=fixture();note=json.loads(note_data)
    domain,copy=32768,32000;next_column=5000
    observed={tuple(e['source']):tuple((c,int(v,16)) for c,v in e['terms']) for e in note['expressions']}
    levels=[];rows=[(canonical([(0,1),(copy,-1)]),())];tree_indices=[];hash_indices=[];page_paths=[]
    outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    params=dict(width=6,ark=[[1+r*6+c for c in range(6)] for r in range(65)],
        mds=[[1+int(r==c) for c in range(6)] for r in range(6)],vectors=[])
    artifact=dict(schema='shieldd.poseidon381.v1',modulus=str(relation.MODULUS),alpha=5,full_rounds=8,
        partial_rounds=57,skip_matrices=0,ark=[[f'{v:064x}' for v in row] for row in params['ark']],
        mds=[[f'{v:064x}' for v in row] for row in params['mds']],vectors=[])
    (directory/'poseidon381-wide.json').write_bytes(encoded(artifact))
    def put(tag,index,lc):
        observed[(tag,index)]=canonical(lc);return source(tag,index)
    def get(ref):return observed[tuple(ref['source'])]
    for ordinal in range(48):
        slot,index=divmod(ordinal,24);spend=note['spends'][slot];start=100000+ordinal*20000
        node=spend['commitment'] if index==0 else levels[-1]['output']
        low,high=[source(*bit) for bit in spend['position_bits'][2*index:2*index+2]]
        siblings=[put(1,1097+3*ordinal+j,[(1100+3*ordinal+j,1)]) for j in range(3)]
        products=[];indices=[0]
        for bit in (low,high):indices.append(len(rows));rows.append((outline(get(bit)),outline(get(bit))))
        def product(bit,delta,j):
            nonlocal next_column
            right=put(2,start+2*j,delta);out=put(2,start+2*j+1,[(next_column,1)])
            auxiliary=((next_column+1,1),);next_column+=2
            a,b,z=map(get,(bit,right,out));indices.extend((len(rows),len(rows)+1))
            rows.extend([(outline(combine(a,b,-1)),auxiliary),(outline(combine(a,b)),combine(auxiliary,z,4))])
            products.append([bit,right,out]);return out
        first,second,third=map(get,siblings);node_lc=get(node)
        ls=product(low,combine(first,node_lc,-1),0);rs=product(low,combine(third,node_lc,-1),1)
        bases=[combine(node_lc,get(ls)),combine(first,get(ls),-1),second,third]
        deltas=[combine(first,bases[0],-1),combine(second,bases[1],-1),
            combine(combine(node_lc,get(rs)),second,-1),canonical((c,-v) for c,v in get(rs))]
        outputs=[product(high,delta,j+2) for j,delta in enumerate(deltas)]
        children=[put(2,start+20+j,combine(base,get(out))) for j,(base,out) in enumerate(zip(bases,outputs))]
        tree_indices.append(indices)
        if slot==0:
            inputs=[{'native':f'{index+1:064x}'},*children]
            before=[{'native':f'{1281:064x}'},*inputs]
            graph=poseidon_graph.permutation(params,[1281,index+1,None,None,None,None])
            refs={};derived={};nodes={};indices=[0]
            for n,operation in enumerate(graph['nodes']):
                if operation['kind']=='input':ref=children[operation['slot']]['source'];lc=get(children[operation['slot']])
                elif operation['kind']=='constant':ref=[0,start+1000+n];lc=canonical([(0,operation['value'])])
                else:
                    ref=[2,start+1000+n];left,right=refs[operation['left']],refs[operation['right']]
                    a,b=derived[operation['left']],derived[operation['right']]
                    nodes[tuple(ref)]=dict(index=ref[1],multiply=operation['kind']=='mul',left=left,right=right)
                    if operation['kind']=='add':lc=combine(a,b)
                    elif all(c==0 for c,_ in a):lc=canonical((c,v*(a[0][1] if a else 0)) for c,v in b)
                    else:
                        lc=((next_column,1),);next_column+=1;indices.append(len(rows))
                        if a==b:rows.append((outline(a),lc))
                        else:
                            auxiliary=((next_column,1),);next_column+=1;indices.append(len(rows)+1)
                            rows.extend([(outline(combine(a,b,-1)),auxiliary),(outline(combine(a,b)),combine(auxiliary,lc,4))])
                refs[n]=ref;derived[n]=lc
            after=[{'source':refs[n]} for n in graph['outputs']];output=after[1]
            boundaries={tuple(child['source']) for child in children};visited=set();pending=[tuple(v['source']) for v in after]
            while pending:
                ref=pending.pop()
                if ref in visited:continue
                visited.add(ref)
                if ref not in boundaries and ref in nodes:pending.extend(tuple(nodes[ref][key]) for key in ('left','right'))
            table={ref:op for ref,op in nodes.items() if ref in visited}
            needed=boundaries|{ref for ref in visited if ref[0]==0}|{tuple(v['source']) for v in after}
            for ref,operation in table.items():
                if operation['multiply'] and operation['left'][0]!=0 and operation['right'][0]!=0:
                    needed.update((ref,tuple(operation['left']),tuple(operation['right'])))
            page_observed={tuple(ref):derived[n] for n,ref in refs.items() if tuple(ref) in needed}
            observed[tuple(output['source'])]=derived[graph['outputs'][1]]
            page=dict(schema='shieldd-transfer-note-hash-block-v1',family='transfer',scope=hashes.SCOPE,
                ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=slot,role='state',level=index,block=0,
                hash=dict(domain=1,inputs=inputs,output=output,blocks=[dict(before=before,after=after)]),
                expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in lc]) for h,lc in sorted(page_observed.items())],
                nodes=sorted(table.values(),key=lambda op:op['index']))
            page_path=directory/f'state-{index}.json';page_path.write_bytes(encoded(page));page_paths.append(page_path)
            hash_indices.append(indices)
            if index==23:
                old=tuple(spend['computed_anchor']['source']);spend['computed_anchor']=output
                note['expressions']=[e for e in note['expressions'] if tuple(e['source'])!=old]
                note['expressions'].append(dict(source=output['source'],terms=[[c,f'{v:064x}'] for c,v in get(output)]))
                del observed[old]
        else:
            output=spend['computed_anchor'] if index==23 else put(2,start+100,[(next_column,1)])
            if index!=23:next_column+=1
        levels.append(dict(slot=slot,level=index,node=node,low=low,high=high,siblings=siblings,
            swaps=[ls,rs],children=children,output=output,products=products))
    records=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]) for i,(a,b) in enumerate(rows)]
    public,blocks=[[1,990]],[[1,991]];digest=blake3()
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+relation.indices(public)+relation.u64(1)+relation.indices(blocks))
    for record in records:digest.update(b'A'+relation.terms(record['a'],domain)+b'B'+relation.terms(record['b'],domain))
    identity=dict(relation_digest=digest.hexdigest(),domain_size=domain,full_rows=len(rows),constant_copy=copy)
    note.update(identity);caller['metadata'].update(identity);note_data=encoded(note)
    obj=dict(schema='shieldd-transfer-note-tree-v1',family='transfer',scope=tree.SCOPE,**identity,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,domain=1,depth=24,levels=levels,
        expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in lc]) for h,lc in sorted(observed.items())],spend=note)
    data=encoded(obj);tree.inspect_metadata(data,note_data,caller)
    for page_path in page_paths:
        page=json.loads(page_path.read_bytes());page.update(identity)
        expressions={tuple(e['source']):e for e in page['expressions']}
        expressions.update((tuple(e['source']),e) for e in note['expressions'])
        page['expressions']=[expressions[h] for h in sorted(expressions)];page_path.write_bytes(encoded(page))
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity['relation_digest'],domain_size=domain,
        stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,public_columns=[1],committed_columns=[[2]],
        source_public=public,source_blocks=[blocks],coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',padding='implicit-all-zero-rows-to-domain-size')
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]))
    verified=relation.inspect(stream,expected_relation=identity['relation_digest'])
    def selected(indices,metadata,**roles):
        return dict(identity=verified,metadata_sha256=hashlib.sha256(metadata).hexdigest(),
            selected_rows=[records[i] for i in indices],**roles)
    tree_selected=[selected(indices,data,slot=i//24,level=i%24) for i,indices in enumerate(tree_indices)]
    hash_selected=[selected(indices,page_paths[i].read_bytes(),slot=0,role='state',level=i,block=0) for i,indices in enumerate(hash_indices)]
    return dict(data=data,note=note_data,caller=caller,artifact=artifact,tree=tree_selected,
        hashes=hash_selected,pages=page_paths,records=records,rows=rows,header=header)
