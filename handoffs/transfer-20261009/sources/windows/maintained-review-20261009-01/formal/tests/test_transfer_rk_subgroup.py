"""Typed RK subgroup fixtures only; no captured/runtime evidence."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_rk_subgroup as rk, transfer_relation as relation, group_rows
from circuits.transfer_balance_rows import canonical, combine


def fixture(change_rows=None):
    domain,constant=4096,4090; nodes=[]; lcs={}; constants={}; rows=[]
    def witness(index):
        h=(1,index); lcs[h]=((3+index,1),); return h
    point=[witness(10),witness(11)];preimage=[witness(100),witness(101)]
    def const(value):
        value%=rk.P
        if value not in constants:
            h=(0,len(constants));constants[value]=h;lcs[h]=canonical([(0,value)])
        return constants[value]
    coefficient=const(rk.D)
    outline=lambda terms:canonical((constant if c == 0 else c,v) for c,v in terms)
    def row(a,b=()):rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in canonical(a)],b=[[c,f'{v:064x}'] for c,v in canonical(b)]))
    row([(0,1),(constant,-1)])
    def op(multiply,left,right):
        index=len(nodes);h=(2,index);a,b=lcs[left],lcs[right]
        nodes.append(dict(index=index,multiply=multiply,left=list(left),right=list(right)))
        if not multiply:z=combine(a,b)
        elif left[0] == 0 or right[0] == 0:
            scalar,other=(a,b) if left[0] == 0 else (b,a)
            factor=scalar[0][1] if scalar else 0;z=canonical((c,v*factor) for c,v in other)
        else:
            z=((1000+2*index,1),)
            if left == right:row(outline(a),z)
            else:
                aux=((1001+2*index,1),)
                row(outline(combine(a,b,-1)),aux);row(outline(combine(a,b)),combine(aux,z,4))
        lcs[h]=z;return h
    def formula(role,inputs):
        graph=group_rows.expected(role);mapped=[]
        for node in graph['nodes']:
            if node['kind']=='input':h=inputs[node['slot']]
            elif node['kind']=='constant':h=const(node['value'])
            else:h=op(node['kind']=='mul',mapped[node['left']],mapped[node['right']])
            mapped.append(h)
        return mapped[graph['output']]
    curve=[formula('curve.left',preimage),formula('curve.right',preimage)]
    row(outline(combine(lcs[curve[0]],lcs[curve[1]],-1)))
    doubles=[];spans=[];before=preimage
    for i in range(3):
        start=len(nodes);inverse=witness(110+i)
        denominator=formula('denominator',before)
        product=op(True,inverse,denominator)
        row(outline(combine(lcs[product],[(0,1)],-1)))
        after=[formula('x',before+[inverse]),formula('y',before+[inverse])]
        doubles.append(list(map(list,before+after)));spans.append([start,len(nodes)]);before=after
    for a,b in zip(point,before):row(outline(combine(lcs[a],lcs[b],-1)))
    inverse=witness(113);product=op(True,inverse,point[0])
    row(outline(combine(lcs[product],[(0,1)],-1)))
    required=set(point+preimage+[coefficient]+curve+[point[0],inverse,product])
    required.update(tuple(h) for double in doubles for h in double)
    required.update((2,i) for start,stop in spans for i in range(start,stop))
    pending=list(required);visited=set()
    while pending:
        h=pending.pop()
        if h in visited:continue
        visited.add(h)
        if h[0] != 2:required.add(h);continue
        node=nodes[h[1]];left,right=tuple(node['left']),tuple(node['right'])
        if node['multiply'] and left[0] != 0 and right[0] != 0:required.update((h,left,right))
        pending.extend((left,right))
    if change_rows:change_rows(rows)
    for i,item in enumerate(rows):item['row']=i
    public,block=[[1,0]],[[1,1]]
    state=blake3();state.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows)))
    state.update(relation.indices(public));state.update(relation.u64(1));state.update(relation.indices(block))
    for item in rows:state.update(b'A'+relation.terms(item['a'],domain)+b'B'+relation.terms(item['b'],domain))
    digest=state.hexdigest()
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=digest,
                domain_size=domain,stored_rows=len(rows),public_inputs=1,committed_blocks=[1],
                constant_column=0,public_columns=[1],committed_columns=[[2]],source_public=public,source_blocks=[block],
                coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
                role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                padding='implicit-all-zero-rows-to-domain-size')
    footer=dict(eof=True,rows=len(rows))
    stream=b''.join((json.dumps(item)+'\n').encode() for item in [header,*rows,footer])
    obj=dict(schema='shieldd-transfer-rk-subgroup-v1',family='transfer',scope=rk.SCOPE,relation_digest=digest,
             domain_size=domain,full_rows=len(rows),constant_copy=constant,
             ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,
             inputs=list(map(list,point+preimage+[coefficient])),curve=list(map(list,curve)),doubles=doubles,
             spans=spans,nonidentity=list(map(list,[point[0],inverse])),nonidentity_product=list(product),nodes=nodes,
             expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in lcs[h]]) for h in sorted(required)])
    accepted=dict(metadata={k:obj[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')},
                  observed={h:lcs[h] for h in point})
    accepted['metadata']['spend']=dict(rk=[dict(source=list(h)) for h in point])
    return obj,accepted,stream


class RkSubgroupTests(unittest.TestCase):
    def data(self,obj):return (json.dumps(obj)+'\n').encode()
    def test_closed_source_formula_rows_and_fresh_allocations(self):
        obj,accepted,stream=fixture();checked=rk.inspect_metadata(self.data(obj),accepted)
        self.assertEqual(len(checked['formulas']['inverse_witnesses']),3)
        extracted=rk.extract(self.data(obj),accepted,io.BytesIO(stream))
        self.assertEqual(extracted['identity']['stored_rows'],obj['full_rows'])
        self.assertEqual(len(extracted['allocation']['witnesses']),6)
        self.assertEqual(set(extracted['allocation']['nonlinear_writes']) & {13,14},set())
    def test_pending_schema_identity_and_exact_coverage_refuse(self):
        obj,accepted,_=fixture()
        for mutate in (lambda o:o.update(ordinary_full_ordered_rows_equal=False),
                       lambda o:o.update(repeated_observations_equal=False),
                       lambda o:o.update(relation_digest='f'*64),
                       lambda o:o.update(extra=True),lambda o:o['expressions'].pop()):
            changed=copy.deepcopy(obj);mutate(changed)
            with self.subTest(mutate=mutate),self.assertRaises(relation.RelationError):rk.inspect_metadata(self.data(changed),accepted)
    def test_chain_source_topology_inverse_alias_and_shared_lc_refuse(self):
        obj,accepted,_=fixture()
        changes=[lambda o:o['doubles'][1][0].__setitem__(1,999),
                 lambda o:o['spans'][1].__setitem__(0,o['spans'][1][0]+1),
                 lambda o:o['nodes'][-1].__setitem__('right',o['inputs'][1]),
                 lambda o:o['nodes'][0].__setitem__('left',[2,o['nodes'][0]['index']]),
                 lambda o:o['inputs'].__setitem__(2,o['inputs'][0])]
        for mutate in changes:
            changed=copy.deepcopy(obj);mutate(changed)
            with self.subTest(mutate=mutate),self.assertRaises(relation.RelationError):rk.inspect_metadata(self.data(changed),accepted)
        changed=copy.deepcopy(accepted);changed['observed'][(1,10)]=((99,1),)
        with self.assertRaisesRegex(relation.RelationError,'shared source LC'):rk.inspect_metadata(self.data(obj),changed)
    def test_missing_changed_original_rows_and_caller_owned_alias_refuse(self):
        for mutate in (lambda rows:rows.pop(),lambda rows:rows[-1]['a'][0].__setitem__(1,f'{2:064x}')):
            obj,accepted,stream=fixture(mutate)
            with self.assertRaisesRegex(relation.RelationError,'missing RK subgroup actual template'):
                rk.extract(self.data(obj),accepted,io.BytesIO(stream))
        obj,accepted,_=fixture();accepted['observed'][(2,9999)]=((103,1),)
        with self.assertRaisesRegex(relation.RelationError,'witness/caller allocation'):rk.inspect_metadata(self.data(obj),accepted)
    def test_duplicate_actual_product_allocation_refuses(self):
        def duplicate(rows):
            pair=next(i for i in range(len(rows)-1) if rows[i]['b'] and rows[i+1]['b'] and rows[i]['b'] != rows[i+1]['b'])
            rows.extend(copy.deepcopy(rows[pair:pair+2]))
        obj,accepted,stream=fixture(duplicate)
        with self.assertRaisesRegex(relation.RelationError,'one exact actual match'):
            rk.extract(self.data(obj),accepted,io.BytesIO(stream))
    def test_malformed_metadata_is_typed_refusal(self):
        obj,accepted,_=fixture()
        for field,value in (('domain_size',True),('inputs',[]),('nodes',None),('expressions',None),
                            ('relation_digest',None),('constant_copy',-1)):
            changed=copy.deepcopy(obj);changed[field]=value
            with self.subTest(field=field),self.assertRaises(relation.RelationError):rk.inspect_metadata(self.data(changed),accepted)


if __name__=='__main__':unittest.main()
