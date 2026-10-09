import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from circuits import transfer_ak_subgroup as ak
from circuits.transfer_relation import RelationError


class AkIngressTests(unittest.TestCase):
    def check_bad(self, value, reason):
        with self.assertRaisesRegex(RelationError, reason):
            ak.inspect_metadata((json.dumps(value)+'\n').encode(), '1'*64,
                                [[1,1990],[1,1977],[1,1978],[2,329976]])

    def test_exact_digest_required(self):
        with self.assertRaisesRegex(RelationError,'exact canonical AK relation'):
            ak.inspect_metadata(b'{}\n',None,[])

    def test_bounded_bytes(self):
        with self.assertRaisesRegex(RelationError,'exceeds 1MiB'):
            ak.inspect_metadata(b' '*(1024*1024+1),'1'*64,[])

    def test_unknown_schema_rejected_after_framing(self):
        self.check_bad({},'unknown AK metadata schema/scope')

    def test_nonobject_rejected(self):
        for value in ([], True, 1):
            self.check_bad(value,'record must be a JSON object')

    def test_truncated_record_is_not_schema_control(self):
        with self.assertRaisesRegex(RelationError,'truncated or empty row framing'):
            ak.inspect_metadata(b'{}','1'*64,[])

    def test_control_harness_rejects_unrelated_framing_failure(self):
        state = {'metadata':{'inputs':[[1,1],[1,2]]}}
        with patch.object(ak,'inspect_metadata',side_effect=[state,RelationError('truncated or empty row framing')]), patch.object(ak,'match_formulas'):
            with self.assertRaisesRegex(RelationError,'control failed for unrelated reason'):
                ak.ingress_controls(b'{}\n',[],'1'*64)


class AkCliTests(unittest.TestCase):
    def run_cli(self, *args):
        import security
        with patch.object(sys,'argv',['security.py','check',*args]), patch.object(security,'check_register',return_value={}):
            return security.main()

    def test_matching_ivk_required(self):
        self.assertEqual(self.run_cli('--relation-export','unused','--expected-relation-digest','1'*64,
                                     '--ak-subgroup-inspection','unused'),1)

    def test_qualification_conflict_rejected(self):
        self.assertEqual(self.run_cli('--ak-subgroup-inspection','unused','--verify-link'),1)

    def test_mixed_reduction_rejected(self):
        self.assertEqual(self.run_cli('--relation-export','unused','--expected-relation-digest','1'*64,
                                     '--ak-subgroup-inspection','unused','--ivk-inspection','unused',
                                     '--ivk-reduction-inspection','unused'),1)

    def test_routes_only_extraction_with_retained_ivk_handles(self):
        handles = [[1,1990],[1,1977],[1,1978],[2,329976]]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'metadata'
            path.write_bytes(b'{}\n')
            with patch('circuits.transfer_ivk_rows.inspect_metadata',return_value={'metadata':{'handles':handles}}), \
                 patch.object(ak,'ingress_controls',return_value={'cases':[]}), \
                 patch.object(ak,'scoped_semantic_controls',return_value={'cases':[],'scope':'selected slice only'}), \
                 patch.object(ak,'extract',return_value={'selected_rows':[{}],'products':[],
                              'metadata_sha256':'2'*64,'scope':'extraction only'}) as extract:
                self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                                             '--ak-subgroup-inspection',str(path),'--ivk-inspection',str(path)),0)
                self.assertEqual(extract.call_args.args[1],handles)
                self.assertEqual(extract.call_args.args[3],'1'*64)


if __name__ == '__main__':
    unittest.main()
