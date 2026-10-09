import io,json,unittest
from unittest.mock import patch
from circuits import transfer_receiver_lifecycle as lifecycle
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine

def record(index,a,b):
    return dict(row=index,a=[[c,f'{v:064x}'] for c,v in canonical(a)],
                b=[[c,f'{v:064x}'] for c,v in canonical(b)])

class ReceiverLifecycleTests(unittest.TestCase):
    def test_direct_zero_product_and_materialized_assertion_are_distinct(self):
        gate=dict(index=0,expected=1,left=((10,1),),right=((20,1),))
        minus,plus=combine(gate['left'],gate['right'],-1),combine(gate['left'],gate['right'])
        first=record(5,minus,[(30,1)])
        second=record(6,plus,[(30,1)])
        _,gates,used=lifecycle._match({},[(gate,minus,plus)],{(minus,None):[first],(plus,None):[second]}, {})
        self.assertEqual(gates[0]['output'],());self.assertEqual(used,{5,6})
        second=record(6,plus,[(30,1),(31,4)]);assertion=record(7,[(31,1)],[])
        _,gates,used=lifecycle._match({},[(gate,minus,plus)],{(minus,None):[first],(plus,None):[second]}, {((31,1),):[assertion]})
        self.assertEqual(gates[0]['output'],((31,1),));self.assertEqual(used,{5,6,7})

    def test_duplicate_or_missing_physical_gate_refuses(self):
        gate=dict(index=2,expected=0);minus=((10,1),);plus=((20,1),)
        first=record(5,minus,[(30,1)]);second=record(6,plus,[(30,1)])
        for candidates in ({(minus,None):[first]}, {(minus,None):[first],(plus,None):[second,record(7,plus,[(30,1)])]}):
            with self.assertRaises(relation.RelationError):lifecycle._match({},[(gate,minus,plus)],candidates,{})

    def test_reversed_materialization_and_nonunit_auxiliary_refuse(self):
        gate=dict(index=2,expected=0);minus=((10,1),);plus=((20,1),)
        for first,second in [(record(7,minus,[(30,1)]),record(6,plus,[(30,1)])),
                             (record(5,minus,[(30,2)]),record(6,plus,[(30,2)]))]:
            with self.assertRaises(relation.RelationError):
                lifecycle._match({},[(gate,minus,plus)],{(minus,None):[first],(plus,None):[second]}, {})

    def test_exact_receiver_layout_and_source_consumer_alias(self):
        refs=[dict(source=[1,i]) for i in range(100,231)]
        observed={(1,i):((i,1),) for i in range(100,231)}
        observed.update({(1,50):((50,1),),(1,44):((44,1),)})
        checked=dict(metadata=dict(scope='receiver',constant_copy=900),observed=observed,
            records={('receiver','lifecycle-bits',0):refs,
                ('receiver','receiver-binding',0):[dict(source=[1,50])]*8,
                ('receiver','membership',0):[dict(source=[1,44])]*5})
        accepted=dict(observed={})
        with patch.object(lifecycle.pages,'inspect_page',return_value=checked):
            selected=lifecycle.boundary(b'manifest',b'roles',accepted)
            self.assertEqual([gate['index'] for gate in selected['gates']],[0,1,2,*range(67,131)])
            self.assertEqual(selected['value'],50)
            observed[(2,300)]=((100,1),)
            with self.assertRaises(relation.RelationError):lifecycle.boundary(b'manifest',b'roles',accepted)

    def test_full_ordinary_shape_and_unique_direct_rows(self):
        selected=dict(checked=dict(metadata=dict(relation_digest='a'*64,domain_size=1024,full_rows=99,constant_copy=900)),
            columns=[100],value=50,weighted=((100,1),),gates=[])
        direct,_=lifecycle._requirements(selected)
        rows=[record(i,*row) for i,row in enumerate(direct)]
        calls=[]
        def inspect(stream,*,expected_relation,row_observer):
            calls.append(expected_relation)
            for row in rows:row_observer(row)
            return dict(relation_digest=expected_relation,domain_size=1024,stored_rows=99)
        with patch.object(lifecycle.relation,'inspect',side_effect=inspect):
            result=lifecycle._retain(io.BytesIO(),selected)
            self.assertEqual(len(calls),1);self.assertEqual(len(result['selected_rows']),3)
            rows.append(record(5,*next(iter(direct))))
            with self.assertRaises(relation.RelationError):lifecycle._retain(io.BytesIO(),selected)

if __name__=='__main__':unittest.main()
