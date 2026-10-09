"""Synthetic original source cone, independent values and complete row stream."""
import json
from blake3 import blake3
from circuits import poseidon_graph,transfer_relation as relation,transfer_recovery_hash as hashes
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_asset_map import Builder
from tests.test_transfer_recovery_capsule import fixture as roles_fixture
from tests.test_transfer_note_spend import encoded


class HashBuilder(Builder):
    def binary(self,a,b,multiply):
        out=super().binary(a,b,multiply)
        if out['source'][0]==2:
            old=tuple(out['source']);new=(2,100000+old[1])
            self.nodes[-1]['index']=new[1];self.expressions[new]=self.expressions.pop(old);out['source']=list(new)
        return out


def fixture(role):
    recovery,output,caller,_=roles_fixture();meta=json.loads(recovery);out=json.loads(output);entry=meta['capsules'][0]
    width,domain,inputs,key=(3,11,entry['shared'],'secret') if role=='secret' else (
        (6,21,[entry['seed'],*entry['capsule'][:2],entry['capsule'][3]],'computed_confirmation') if role=='confirmation' else
        (3,10,[entry['seed'],{'native':f'{int(role=="blinding-stream"):064x}'}],
         'blinding_stream' if role=='blinding-stream' else 'amount_stream'))
    params=dict(width=width,ark=[[1+r*width+c for c in range(width)] for r in range(65)],
                mds=[[1+int(r==c) for c in range(width)] for r in range(width)],vectors=[])
    artifact=dict(schema='shieldd.poseidon381.v1',modulus=str(relation.MODULUS),alpha=5,full_rounds=8,partial_rounds=57,
        skip_matrices=0,ark=[[f'{v:064x}' for v in row] for row in params['ark']],
        mds=[[f'{v:064x}' for v in row] for row in params['mds']],vectors=[])
    b=HashBuilder()
    known={tuple(e['source']):tuple((c,int(v,16)) for c,v in e['terms']) for e in meta['expressions']}
    b.expressions.update(known)
    for lc in known.values():
        for c,_ in lc:b.rho[c]=(23*c+13)%relation.MODULUS
    b.rho[0]=b.rho[32000]=1
    before=[{'native':f'{domain+256*len(inputs):064x}'},*inputs]
    before.extend([{'native':f'{0:064x}'}]*(width-len(before)))
    source_inputs=[ref for ref in before if 'source' in ref]
    graph=poseidon_graph.permutation(params,[int(ref['native'],16) if 'native' in ref else None for ref in before]);refs={}
    for i,node in enumerate(graph['nodes']):
        if node['kind']=='input':ref=source_inputs[node['slot']]
        elif node['kind']=='constant':ref=b.constant(node['value'])
        else:ref=(b.mul if node['kind']=='mul' else b.add)(refs[node['left']],refs[node['right']])
        refs[i]=ref
    after=[refs[i] for i in graph['outputs']];old=tuple(entry[key]['source']);entry[key]=after[1]
    del known[old];known[tuple(after[1]['source'])]=b.lc(after[1])
    downstream={'secret':('computed_c2','seed'),'amount-stream':('computed_amount','amount'),
                'blinding-stream':('computed_blinding','blinding')}
    if role in downstream:
        derived,input_key=downstream[role];known[tuple(entry[derived]['source'])]=combine(b.lc(entry[input_key]),b.lc(after[1]))
    meta['expressions']=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in lc]) for h,lc in sorted(known.items())]
    roots={tuple(r['source']) for r in before if 'source' in r};table={node['index']:node for node in b.nodes}
    visited=set();pending=[tuple(r['source']) for r in after]
    while pending:
        ref=pending.pop()
        if ref in visited:continue
        visited.add(ref)
        if ref not in roots and ref[0]==2:pending.extend(tuple(table[ref[1]][k]) for k in ('left','right'))
    nodes=[n for n in b.nodes if (2,n['index']) in visited and (2,n['index']) not in roots]
    required=set(known)|roots|{tuple(r['source']) for r in after}|{r for r in visited if r[0]==0}
    for node in nodes:
        if node['multiply'] and node['left'][0]!=0 and node['right'][0]!=0:
            required.update(((2,node['index']),tuple(node['left']),tuple(node['right'])))
    outlined=lambda lc:canonical((32000 if c==0 else c,v) for c,v in lc)
    rows=[(canonical([(0,1),(32000,-1)]),()),*[(outlined(a),outlined(z)) for a,z in b.rows]]
    records=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in z]) for i,(a,z) in enumerate(rows)]
    public,blocks=[[1,990]],[[1,991]];digest=blake3()
    digest.update(relation.NAMESPACE+relation.u64(32768)+relation.u64(len(rows))+relation.indices(public)+relation.u64(1)+relation.indices(blocks))
    for row in records:digest.update(b'A'+relation.terms(row['a'],32768)+b'B'+relation.terms(row['b'],32768))
    identity=dict(relation_digest=digest.hexdigest(),domain_size=32768,full_rows=len(rows),constant_copy=32000)
    meta.update(identity);out.update(identity);caller['metadata'].update(identity)
    observed=dict(b.expressions);observed.update(known)
    page=dict(schema='shieldd-transfer-recovery-hash-block-v1',family='transfer',scope=hashes.SCOPE,**identity,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,slot=0,role=role,level=0,block=0,
        hash=dict(domain=domain,inputs=inputs,output=after[1],blocks=[dict(before=before,after=after)]),nodes=nodes,
        expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in observed[h]]) for h in sorted(required)])
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=digest.hexdigest(),domain_size=32768,
        stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,public_columns=[1],committed_columns=[[2]],
        source_public=public,source_blocks=[blocks],coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',padding='implicit-all-zero-rows-to-domain-size')
    return encoded(page),encoded(meta),encoded(out),caller,artifact,b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]),b,params
