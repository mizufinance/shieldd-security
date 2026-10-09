import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from circuits import transfer_ivk_rows as ivk
from circuits.transfer_relation import RelationError


class IvkMetadataTests(unittest.TestCase):
    """Synthetic parser/source-template controls; not circuit security tests."""
    def setUp(self):
        one = f'{1:064x}'
        seven = f'{7:064x}'
        self.graph = {'arity':3, 'output':6, 'nodes':[
            {'kind':'input','slot':0},{'kind':'input','slot':1},{'kind':'input','slot':2},
            {'kind':'constant','value':7},{'kind':'add','left':0,'right':3},
            {'kind':'mul','left':4,'right':1},{'kind':'add','left':5,'right':2}]}
        self.metadata = {'schema':'shieldd-transfer-ivk-inspection-v1', 'relation_digest':'a'*64,
            'domain_size':32,'stored_rows':20,'ordinary_full_ordered_rows_equal':True,
            'scope':ivk.SCOPE,'constant_copy':19,'domain':16,'arity':3,
            'handles':[[1,0],[1,1],[1,2],[2,6]],
            'expressions':[{'source':source,'terms':terms} for source,terms in [
                ([0,3],[[0,seven]]),([1,0],[[3,one]]),([1,1],[[4,one]]),
                ([1,2],[[5,one]]),([2,4],[[0,seven],[3,one]]),([2,5],[[10,one]]),
                ([2,6],[[5,one],[10,one]])]],
            'nodes':[{'index':index,'multiply':multiply,'left':left,'right':right}
                     for index,multiply,left,right in [(4,False,[1,0],[0,3]),
                        (5,True,[2,4],[1,1]),(6,False,[2,5],[1,2])]]}
    def inspect(self,obj=None,expected='a'*64):
        data=(json.dumps(self.metadata if obj is None else obj)+'\n').encode()
        with patch.object(ivk.poseidon_graph,'parameters',return_value={}), \
             patch.object(ivk.poseidon_graph,'expected',return_value=self.graph):
            return ivk.inspect_metadata(data,Path('.'),expected)
    def test_valid_synthetic_cone(self):
        checked=self.inspect()
        self.assertEqual(checked['derived'][(2,6)],((5,1),(10,1)))
        self.assertIn('row certificates',checked['scope'])
    def test_adapted_export_retains_exact_input_mapping(self):
        checked=self.inspect()
        source=copy.deepcopy(checked['source'])
        for node in source.values():
            if node['kind']=='constant':node['value']=f"{node['value']:064x}"
        names=checked['source_names']
        export={'hash_scope':'transfer-ivk-only','subject':'actual Transfer IVK hash dependency cone',
            'scalar_encoding':'canonical-big-endian-32','modulus_minus_one':f'{ivk.P-1:064x}',
            'input_source_handles':self.metadata['handles'][:3],
            'input_role_provenance':'formal input renaming; original captured handles retained',
            'calls':[{'role':'authorization.ivk','domain':16,'inputs':['w0','w1','w2'],
                'output':names[checked['handles'][3]],'source':source}],
            'expressions':[{'source':names[index],'kind':'linear',
                'terms':[[column,f'{value:064x}'] for column,value in terms]}
                for index,terms in checked['derived'].items()]}
        with patch.object(ivk.poseidon_graph,'parameters',return_value={}), \
             patch.object(ivk.poseidon_graph,'expected',return_value=self.graph):
            self.assertEqual(len(ivk.poseidon_graph.match_export(export,Path('.'))),1)
            wrong=copy.deepcopy(export);wrong['input_source_handles'][0][1]=3
            with self.assertRaisesRegex(ValueError,'mapping changed'):
                ivk.poseidon_graph.match_export(wrong,Path('.'))
            wrong=copy.deepcopy(export);wrong['calls'][0]['inputs']=['w1','w0','w2']
            with self.assertRaisesRegex(ValueError,'order changed'):
                ivk.poseidon_graph.match_export(wrong,Path('.'))

    def test_exact_digest_required(self):
        for value in (None,'A'*64,'short',True):
            with self.subTest(value=value), self.assertRaises(RelationError): self.inspect(expected=value)
    def test_aliases_scope_and_wrong_shapes_rejected(self):
        changes=[('domain',True),('arity',3.0),('domain_size',32.0),('constant_copy',True),
                 ('scope','other'),('handles',{}),('nodes',{}),('expressions',{})]
        for key,value in changes:
            obj=copy.deepcopy(self.metadata);obj[key]=value
            with self.subTest(key=key), self.assertRaises(RelationError): self.inspect(obj)
    def test_missing_extra_duplicate_forward_and_role_mutations(self):
        objects=[]
        obj=copy.deepcopy(self.metadata);obj['nodes'].pop();objects.append(obj)
        obj=copy.deepcopy(self.metadata);obj['nodes'].append({'index':7,'multiply':False,'left':[1,0],'right':[1,1]});objects.append(obj)
        obj=copy.deepcopy(self.metadata);obj['expressions'].append(copy.deepcopy(obj['expressions'][-1]));objects.append(obj)
        obj=copy.deepcopy(self.metadata);obj['nodes'][0]['left']=[2,5];objects.append(obj)
        obj=copy.deepcopy(self.metadata);obj['handles'][1]=obj['handles'][0];objects.append(obj)
        obj=copy.deepcopy(self.metadata);obj['expressions'][1]['source']=[1,3];objects.append(obj)
        obj=copy.deepcopy(self.metadata);obj['nodes'][0]['multiply']=1;objects.append(obj)
        for i,obj in enumerate(objects):
            with self.subTest(i=i), self.assertRaises(RelationError): self.inspect(obj)
    def test_linear_and_constant_observation_mutations(self):
        for index,column,value in [(4,3,2),(0,1,7),(1,3,2)]:
            obj=copy.deepcopy(self.metadata);obj['expressions'][index]['terms']=[[column,f'{value:064x}']]
            with self.subTest(index=index), self.assertRaises(RelationError): self.inspect(obj)


if __name__=='__main__': unittest.main()
