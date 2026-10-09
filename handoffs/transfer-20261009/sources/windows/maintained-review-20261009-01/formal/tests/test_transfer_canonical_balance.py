import copy
import io
import json
import struct
import unittest
from blake3 import blake3
from circuits import transfer_canonical_balance as target
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine


class CanonicalBalanceTests(unittest.TestCase):
    def setUp(self):
        p=target.P
        self.metadata={'schema':'shieldd-transfer-canonical-balance-inspection-v1',
            'relation_digest':'','domain_size':8192,'stored_rows':0,
            'ordinary_full_ordered_rows_equal':True,
            'scope':'source handles and pre-outline linear combinations only; semantic row certificates remain open',
            'constant_copy':5000,'value':[1,0],'bits':[[1,i+1] for i in range(252)],
            'endpoint':None,'steps':[],'expressions':[],'nodes':[]}
        expressions={(1,0):((3,1),)}
        expressions.update({(1,i+1):((4+i,1),) for i in range(252)})
        self.rows=[]
        def row(a,b=()):
            self.rows.append({'row':len(self.rows),'a':[[c,f'{v:064x}'] for c,v in canonical(a)],
                'b':[[c,f'{v:064x}'] for c,v in canonical(b)]})
        def outline(lc): return canonical([(5000 if c==0 else c,v) for c,v in lc])
        row([(0,1),(5000,-1)])
        for i in range(252): row([(4+i,1)],[(4+i,1)])
        row([(4+i,2**i) for i in range(252)]+[(3,-1)])
        row([(2,1),(3,-1)])
        previous={'native':f'{1:064x}'};before=((0,1),);previous_node=[0,1]
        for i in range(252):
            bit=(target.ORDER-1)>>i&1;left=((4+i,1),)
            factor=left if bit else combine([(0,1)],left,-1)
            product=factor if i==0 else ((1001+i,1),)
            after=combine(product,combine([(0,1)],left,-1)) if bit else product
            n=i*4
            factor_id=[2,n];product_id=[2,n+1];both_id=[2,n+2];after_id=[2,n+3]
            self.metadata['nodes'] += [
                {'index':n,'multiply':False,'left':[1,i+1],'right':[0,0]},
                {'index':n+1,'multiply':True,'left':previous_node,'right':factor_id},
                {'index':n+2,'multiply':False,'left':[1,i+1],'right':[0,1]},
                {'index':n+3,'multiply':False,'left':product_id,'right':both_id}]
            expressions[(2,n)]=factor;expressions[(2,n+1)]=product;expressions[(2,n+3)]=after
            step=[previous,{'source':[1,i+1]},{'native':f'{bit:064x}'},
                  {'source':factor_id},{'source':product_id},{'source':after_id}]
            self.metadata['steps'].append(step)
            if i:
                aux=((2000+i,1),)
                row(outline(combine(before,factor,-1)),aux)
                row(outline(combine(before,factor)),combine(aux,outline(product),4))
            previous={'source':after_id};previous_node=after_id;before=after
        self.metadata['endpoint']=previous['source']
        # Deliberately use the reversed zero assertion orientation.
        row(outline(combine([(0,1)],before,-1)))
        self.metadata['expressions']=[{'source':list(k),'terms':[[c,f'{v:064x}'] for c,v in terms]}
            for k,terms in sorted(expressions.items())]

    def run_fixture(self,metadata=None,rows=None,expected=True):
        m=copy.deepcopy(self.metadata if metadata is None else metadata)
        rows=self.rows if rows is None else rows
        u64=lambda x:struct.pack('>Q',x);u32=lambda x:struct.pack('>I',x)
        data=relation.NAMESPACE+u64(8192)+u64(len(rows))+u64(1)+b'\x01'+u32(1000)+u64(1)+u64(1)+b'\x01'+u32(0)
        for row in rows:
            for tag,terms in [(b'A',row['a']),(b'B',row['b'])]:
                data+=tag+u64(len(terms))+b''.join(u32(c)+bytes.fromhex(v) for c,v in terms)
        digest=blake3(data).hexdigest();m.update(relation_digest=digest,stored_rows=len(rows))
        header={'schema':'shieldd-transfer-relation-v1','family':'transfer','relation_digest':digest,'domain_size':8192,
            'stored_rows':len(rows),'public_inputs':1,'committed_blocks':[1],'constant_column':0,
            'public_columns':[1],'committed_columns':[[2]],'source_public':[[1,1000]],'source_blocks':[[[1,0]]],
            'coefficient_encoding':'canonical-big-endian-32','field_modulus':str(target.P),
            'role_provenance':'constant0/public prefix and committed_start=1+public_count in exact compiler',
            'padding':'implicit-all-zero-rows-to-domain-size'}
        encode=lambda x:json.dumps(x).encode()+b'\n'
        stream=io.BytesIO(b''.join(map(encode,[header,*rows,{'eof':True,'rows':len(rows)}])))
        result=target.inspect(encode(m),stream,digest if expected else None)
        self.last_metadata=encode(m)
        return result

    def test_selected_actual_templates(self):
        result=self.run_fixture()
        self.assertEqual(len(result['templates']),256)
        self.assertEqual(len(result['products']),251)
        self.assertEqual(len(result['selected_rows']),758)

    def test_missing_committed_link_and_product_rejected(self):
        for index in [254,255]:
            rows=copy.deepcopy(self.rows);rows[index]['a']=[];rows[index]['b']=[]
            with self.assertRaises(relation.RelationError):self.run_fixture(rows=rows)

    def test_native_order_adjacency_and_witness_mapping_rejected(self):
        variants=[]
        m=copy.deepcopy(self.metadata);m['steps'][2][0]=m['steps'][0][0];variants.append(m)
        m=copy.deepcopy(self.metadata);m['steps'][0][2]['native']=f'{1:064x}';variants.append(m)
        m=copy.deepcopy(self.metadata);m['expressions'][0]['source']=[1,999];variants.append(m)
        for m in variants:
            with self.assertRaises(relation.RelationError):self.run_fixture(metadata=m)

    def test_malformed_metadata_rejected(self):
        for field,value in [('scope','wrong'),('bits',{}),('steps',{}),('constant_copy',True),('nodes',[None]),('expressions',[None])]:
            m=copy.deepcopy(self.metadata);m[field]=value
            with self.assertRaises(relation.RelationError):self.run_fixture(metadata=m)
        with self.assertRaises(relation.RelationError):self.run_fixture(expected=False)

    def test_canonical_selected_semantic_controls(self):
        checked=self.run_fixture()
        controls=target.scoped_canonical_controls(self.last_metadata,checked)
        self.assertEqual(len(controls['cases']),4)
        self.assertTrue(all(c['retained_selected_rows_satisfied'] for c in controls['cases']))
