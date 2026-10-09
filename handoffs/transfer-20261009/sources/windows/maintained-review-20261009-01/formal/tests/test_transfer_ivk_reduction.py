import json
import unittest
from unittest.mock import patch
from circuits import transfer_ivk_reduction as reduction
from circuits.transfer_relation import RelationError


class ReductionIngressTests(unittest.TestCase):
    def test_requires_exact_digest_before_metadata(self):
        for digest in (None, True, '', 'A'*64, '0'*63):
            with self.subTest(digest=digest), self.assertRaises(RelationError):
                reduction.inspect_metadata(b'{}',{},digest)

    def test_metadata_bytes_and_finite_bound(self):
        for data in ('{}', bytearray(b'{}'), b' '*(2**20+1)):
            with self.subTest(kind=type(data)), self.assertRaises(RelationError):
                reduction.inspect_metadata(data,{},'0'*64)

    def test_closed_schema_rejects_unexpected_shape(self):
        for value in ({}, {'schema':'shieldd-transfer-ivk-reduction-inspection-v1'}, [], True):
            expected='reduction schema/scope mismatch' if isinstance(value,dict) else 'record must be a JSON object'
            with self.subTest(value=value), self.assertRaises(RelationError) as rejected:
                reduction.inspect_metadata((json.dumps(value)+'\n').encode(),{},'0'*64)
            self.assertEqual(str(rejected.exception),expected)

    def test_controls_refuse_unrelated_rejection(self):
        original={'quotient_bits':[[1,1],[1,2]]}
        with patch.object(reduction,'inspect_metadata',side_effect=[None,RelationError('unrelated framing failure')]), \
             patch.object(reduction.relation,'record',return_value=original):
            with self.assertRaisesRegex(RelationError,'wrong ingress rejection cause'):
                reduction.ingress_controls(b'{}\n',{},'0'*64)

    def test_terminal_literal_is_exact_basefield_tail(self):
        self.assertEqual(reduction.TAIL,43182373549099571680785400801115150921)
        self.assertGreater(reduction.TAIL,0)
        self.assertLess(reduction.TAIL,reduction.ORDER)


if __name__ == '__main__':
    unittest.main()
