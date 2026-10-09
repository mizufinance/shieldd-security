"""Synthetic assertion rows; no real replay, hash semantics or kernel credit."""
import copy, unittest
from unittest.mock import patch
from circuits import transfer_statement_binding as binding
from circuits.transfer_relation import RelationError


def selected():
    metadata = dict(relation_digest='ab'*32, domain_size=262144, full_rows=200770, constant_copy=200692)
    return dict(checked=dict(metadata=metadata), output=((600,1),), claimed=((22737,1),),
                delta=binding.combine(((600,1),),((22737,1),),-1), metadata_sha256='01'*32,
                role_page_sha256='02'*32, final_page_sha256='03'*32)


def fixture(reverse=False):
    s = selected(); delta = s['delta']
    if reverse: delta = binding.canonical((c,-v) for c,v in delta)
    raw = [(binding.canonical([(0,1),(200692,-1)]),()),(delta,())]
    x=dict(metadata_sha256=s['metadata_sha256'], role_page_sha256=s['role_page_sha256'],final_page_sha256=s['final_page_sha256'],
           identity=dict(relation_digest='ab'*32,domain_size=262144,stored_rows=200770),
           selected_rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[]) for i,(a,b) in enumerate(raw)])
    return s,x


class StatementBindingTests(unittest.TestCase):
    def test_direct_and_reversed_actual_assertion_orientation(self):
        for reverse in (False,True):
            s,x=fixture(reverse)
            with patch.object(binding,'_selected',return_value=s):
                source=binding.generate(b'm',b'r',b'f',x,{},None)
            self.assertEqual(source.count('#print axioms'),2)
            self.assertIn('satisfied : Satisfies rho rawRows',source)
            self.assertIn('computed_equals_claimed',source)
            self.assertEqual(').symm' in source,reverse)

    def test_wrong_row_duplicate_and_changed_page_identity_refused(self):
        for mode in ('row','extra','page','digest'):
            s,x=fixture();bad=copy.deepcopy(x)
            if mode=='row':bad['selected_rows'][1]['a'][0][0]+=1
            elif mode=='extra':
                row=copy.deepcopy(bad['selected_rows'][1]);row['row']=2;bad['selected_rows'].append(row)
            elif mode=='page':bad['final_page_sha256']='04'*32
            else:bad['identity']['relation_digest']='cd'*32
            with patch.object(binding,'_selected',return_value=s):
                with self.assertRaises(RelationError):binding.generate(b'm',b'r',b'f',bad,{},None)

    def test_claim_is_not_substituted_for_computed_output(self):
        metadata=dict(records=[],calls=[],relation_digest='ab'*32,domain_size=262144,full_rows=200770,constant_copy=200692)
        claim={'source':[1,22734]};output={'source':[2,777]}
        role=dict(metadata=metadata,records={('statement','interface',0):[claim,{'source':[1,6]}]},observed={(1,22734):((22737,1),)},)
        for alias in (True,False):
            last=dict(metadata={**metadata,'hash':{'output':output}},observed={(2,777):((22737 if alias else 600,1),)})
            with patch.object(binding.pages,'inspect_manifest',return_value=dict(scope='statement',pages=[None]*14)),patch.object(binding.pages,'inspect_page',side_effect=[role,last]):
                if alias:
                    with self.assertRaisesRegex(RelationError,'claimed LC alias'):binding._selected(b'm',b'r',b'f',dict(metadata=metadata),None)
                else:
                    s=binding._selected(b'm',b'r',b'f',dict(metadata=metadata),None)
                    self.assertEqual(s['claimed'],((22737,1),));self.assertEqual(s['output'],((600,1),))

if __name__=='__main__':unittest.main()
