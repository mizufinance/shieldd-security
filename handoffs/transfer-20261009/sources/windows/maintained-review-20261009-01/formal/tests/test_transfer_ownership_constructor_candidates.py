"""Refusal and bounded staging controls, without synthetic qualification."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_constructor_candidates as generator
from circuits.transfer_relation import RelationError


def fixture():
    checked=dict(metadata=dict(window_start=0,window_count=1,relation_digest='a'*64,
        domain_size=64,full_rows=32),windows=[None])
    selected=dict(identity=dict(schema='shieldd-transfer-relation-v1',relation_digest='a'*64,
        domain_size=64,stored_rows=32),selected_rows=[])
    return checked,selected


class ConstructorCandidateTests(unittest.TestCase):
    def test_invalid_chunk_or_relation_refuses_before_rendering(self):
        for mutation in ('start','count','windows','digest','domain','rows','schema'):
            checked,selected=copy.deepcopy(fixture())
            if mutation=='start':checked['metadata']['window_start']=True
            elif mutation=='count':checked['metadata']['window_count']=17
            elif mutation=='windows':checked['windows']=[]
            elif mutation=='digest':selected['identity']['relation_digest']='b'*64
            elif mutation=='domain':selected['identity']['domain_size']=True
            elif mutation=='rows':checked['metadata']['full_rows']=False
            else:selected['identity']['schema']='pending'
            with self.subTest(mutation=mutation),self.assertRaises(RelationError), \
                    patch.object(generator.material,'generate') as material:
                next(generator.iter_candidates(checked,selected))
            material.assert_not_called()

    def test_duplicate_stage_names_refuse_and_all126_join_is_mandatory(self):
        checked,selected=fixture()
        with patch.object(generator.material,'generate',return_value=[('same','source'),('same','source')]):
            candidates=generator.iter_candidates(checked,selected)
            self.assertEqual(next(candidates),('same','source'))
            with self.assertRaises(RelationError):next(candidates)
        with self.assertRaises(RelationError):generator.validate_all_chunks([checked],[])
        with self.assertRaises(RelationError):generator.validate_all_chunks([],[])


if __name__=='__main__':
    unittest.main()
