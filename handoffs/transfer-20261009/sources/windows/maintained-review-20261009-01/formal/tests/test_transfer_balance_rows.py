import copy
import io
import json
import struct
import unittest
from blake3 import blake3
from circuits import transfer_balance_rows as balance
from circuits import transfer_relation as relation


class BalanceRowTests(unittest.TestCase):
    def setUp(self):
        p = balance.P
        w = lambda i: [1, i]
        n = lambda i: [2, i]
        c = lambda i: [0, i]
        expressions = {(1, i): ((i+3, 1),) for i in range(647)}
        expressions.update({(0, 0): ((0, p-1),), (0, 1): ((0, p-2),),
            (2, 0): ((3, 1), (4, 1)), (2, 1): ((5, 1), (6, 1)),
            (2, 2): ((5, p-1), (6, p-1)), (2, 3): ((3, 1), (4, 1), (5, p-1), (6, p-1)),
            (2, 4): ((700, 1),), (2, 5): ((700, p-2),), (2, 6): ((8, 1), (700, p-2))})
        handles = [{'role': 'amount', 'values': [w(i)], 'bits': [w(6+i*128+j) for j in range(128)]} for i in range(4)]
        handles.append({'role': 'signed', 'values': [n(3), w(4), w(5), n(6)], 'bits': [w(518+j) for j in range(129)]})
        triples = [(False,w(0),w(1)), (False,w(2),w(3)), (True,n(1),c(0)),
                   (False,n(0),n(2)), (True,w(4),w(5)), (True,n(4),c(1)), (False,w(5),n(5))]
        self.metadata = {'schema': 'shieldd-transfer-balance-inspection-v1', 'relation_digest': '',
            'domain_size': 1024, 'stored_rows': 0, 'constant_copy': 702,
            'ordinary_full_ordered_rows_equal': True,
            'scope': 'source handles and pre-outline linear combinations only; semantic row certificates remain open',
            'handles': handles,
            'expressions': [{'source': list(key), 'terms': [[i, f'{v:064x}'] for i,v in terms]} for key,terms in sorted(expressions.items())],
            'nodes': [{'index': i, 'multiply': multiply, 'left': left, 'right': right} for i,(multiply,left,right) in enumerate(triples)]}
        self.rows = []
        def row(a, b=()):
            self.rows.append({'row': len(self.rows), 'a': [[i,f'{v:064x}'] for i,v in balance.canonical(a)],
                              'b': [[i,f'{v:064x}'] for i,v in balance.canonical(b)]})
        row([(0,1),(702,-1)])
        for i,item in enumerate(handles):
            value = item['values'][0] if i < 4 else item['values'][2]
            bits = item['bits']
            for bit in bits: row(expressions[tuple(bit)], expressions[tuple(bit)])
            terms = [(bit[1]+3,2**j) for j,bit in enumerate(bits)]
            row(balance.combine(terms,expressions[tuple(value)],-1))
        row(expressions[(1,4)],expressions[(1,4)])
        row(balance.combine(expressions[(2,3)],expressions[(2,6)],-1))
        row([(7,1),(8,-1)],[(701,1)])
        row([(7,1),(8,1)],[(700,4),(701,1)])

    def run_fixture(self, metadata=None, rows=None):
        rows = self.rows if rows is None else rows
        metadata = copy.deepcopy(self.metadata if metadata is None else metadata)
        u64 = lambda value: struct.pack('>Q',value)
        u32 = lambda value: struct.pack('>I',value)
        preimage = (relation.NAMESPACE+u64(1024)+u64(len(rows))+u64(1)+b'\x01'+u32(1000)
                    +u64(1)+u64(1)+b'\x01'+u32(1001))
        for row in rows:
            for tag,terms in [(b'A',row['a']),(b'B',row['b'])]:
                preimage += tag+u64(len(terms))+b''.join(u32(i)+bytes.fromhex(v) for i,v in terms)
        digest = blake3(preimage).hexdigest()
        metadata.update(relation_digest=digest,stored_rows=len(rows))
        header = {'schema':'shieldd-transfer-relation-v1','family':'transfer','relation_digest':digest,
            'domain_size':1024,'stored_rows':len(rows),'public_inputs':1,'committed_blocks':[1],
            'constant_column':0,'public_columns':[1],'committed_columns':[[2]],
            'source_public':[[1,1000]],'source_blocks':[[[1,1001]]],
            'coefficient_encoding':'canonical-big-endian-32','field_modulus':str(balance.P),
            'role_provenance':'constant0/public prefix and committed_start=1+public_count in exact compiler',
            'padding':'implicit-all-zero-rows-to-domain-size'}
        encode = lambda value: json.dumps(value).encode()+b'\n'
        stream = io.BytesIO(b''.join(map(encode,[header,*rows,{'eof':True,'rows':len(rows)}])))
        return balance.inspect(encode(metadata),stream,digest)

    def test_positive_selected_templates_and_product_pair(self):
        result = self.run_fixture()
        self.assertEqual(len(result['templates']),649)
        self.assertEqual(len(result['products']),1)

    def test_selected_row_semantic_omission_assignments(self):
        result = self.run_fixture()
        metadata = copy.deepcopy(self.metadata)
        controls = balance.scoped_omission_controls(json.dumps(metadata).encode()+b'\n',result)
        self.assertEqual(len(controls['cases']),6)
        self.assertTrue(all(case['remaining_selected_rows_satisfied'] for case in controls['cases']))

    def test_missing_boolean_reconstruction_and_product_templates_rejected(self):
        for i in [1,129,len(self.rows)-1]:
            rows = copy.deepcopy(self.rows)
            rows[i]['a'] = []
            rows[i]['b'] = []
            with self.assertRaisesRegex(relation.RelationError,'missing actual template|missing paired product'):
                self.run_fixture(rows=rows)

    def test_wrong_difference_or_signed_source_polynomial(self):
        for node in [3,6]:
            metadata = copy.deepcopy(self.metadata)
            metadata['nodes'][node]['right'] = [1,5]
            with self.assertRaisesRegex(relation.RelationError,'source difference|source selection'):
                self.run_fixture(metadata=metadata)

    def test_aliases_duplicates_extra_and_missing_nodes(self):
        variants = []
        for field,value in [('constant_copy',True),('domain_size',1024.0)]:
            item = copy.deepcopy(self.metadata); item[field]=value; variants.append(item)
        item = copy.deepcopy(self.metadata); item['expressions'].append(item['expressions'][-1]); variants.append(item)
        item = copy.deepcopy(self.metadata); item['expressions'][2]['source']=[1,999]; variants.append(item)
        item = copy.deepcopy(self.metadata); item['nodes'].pop(); variants.append(item)
        item = copy.deepcopy(self.metadata); item['nodes'][0]['multiply']=0; variants.append(item)
        item = copy.deepcopy(self.metadata); item['handles'][1]['bits'][0]=item['handles'][0]['bits'][0]; variants.append(item)
        for metadata in variants:
            with self.assertRaises(relation.RelationError): self.run_fixture(metadata=metadata)
