import unittest
from circuits import transfer_epk_fixed as epk,transfer_relation as relation

class EpkCallerQualificationTests(unittest.TestCase):
    def fixture(self):
        identity=dict(relation_digest='a'*64,domain_size=262144,full_rows=200770,constant_copy=200692)
        caller=dict(identity,schema='shieldd-transfer-authorization-roles-v1',family='transfer',
            ordinary_full_ordered_rows_equal=True,spend={})
        return dict(metadata=caller,observed={}),identity
    def test_uses_real_typed_caller_abi_without_invented_repeat_flag(self):
        roles,parent=self.fixture()
        self.assertIs(epk._qualified_caller_identity(roles,parent),roles['metadata'])
        self.assertNotIn('repeated_observations_equal',roles['metadata'])
    def test_refuses_false_identity_missing_ordinary_and_fabricated_repeat(self):
        for edit in ['false','identity','schema','repeat']:
            with self.subTest(edit=edit):
                roles,parent=self.fixture();caller=roles['metadata']
                if edit=='false':caller['ordinary_full_ordered_rows_equal']=False
                elif edit=='identity':caller['full_rows']-=1
                elif edit=='schema':caller['schema']='shieldd-transfer-epk-fixed-v1'
                else:caller['repeated_observations_equal']=True
                with self.assertRaises(relation.RelationError):epk._qualified_caller_identity(roles,parent)
