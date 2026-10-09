import io
import json
import unittest
from circuits import transfer_fixed_spend as fixed, generate_transfer_fixed_spend as generate
from circuits.transfer_relation import RelationError
from tests.fixed_spend_fixture import full_fixture


class FullFixedSpendTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.captures,cls.roles,cls.stream=full_fixture()
        cls.extractions=[fixed.extract_rows(data,cls.roles,io.BytesIO(cls.stream),include_canonical=i==0)
                         for i,data in enumerate(cls.captures)]

    def test_exact126_single_assignment_symbolic_composition(self):
        checked=[fixed.inspect_metadata(data,self.roles) for data in self.captures]
        self.assertEqual(fixed.join_chunks(checked)['windows'],126)
        source=generate.generate_full(self.captures,self.roles,json.loads(json.dumps(self.extractions)))
        self.assertIn('GroupFixedChunks.chunks_trace',source)
        self.assertIn('GroupFixedWindows.fixed_trace_scalar_coordinates',source)
        self.assertIn('GroupNativeMultiply.native_multiply_coordinates',source)
        for name in ('actual_fixed_scalar','actual_fixed_canonical','actual_fixed_native','actual_fixed_encoded_native',
                     'actual_fixed_native_codec','actual_fixed_native_bytes','actual_randomizer_byte_bits'):
            self.assertIn('#check @'+name,source);self.assertIn('#print axioms '+name,source)
        self.assertNotIn('sorry',source);self.assertNotIn('native_decide',source)
        self.assertIn('TransferReduction.decode_canonical_cast codec',source)
        self.assertIn('SPEND_AUTH',source)
        self.assertIn('blst_bendian_from_scalar',source)
        self.assertIn('codec.decode (eval rho RuntimeTransferRandomizer.privateValue)',source)
        self.assertIn('(writer : GroupByteCodec.BEWrite codec)',source)
        self.assertIn('GroupByteCodec.reader (writer.encode',source)

    def test_missing_reordered_and_unreplayed_chunks_refuse(self):
        for captures,extractions in ((self.captures[:-1],self.extractions[:-1]),
             (self.captures[::-1],self.extractions[::-1]),(self.captures,self.extractions[::-1])):
            with self.subTest(order=len(captures)),self.assertRaises(RelationError):
                generate.generate_full(captures,self.roles,extractions)

    def test_canonical_selection_is_indispensable(self):
        extractions=json.loads(json.dumps(self.extractions));extractions[0]['include_canonical']=False
        with self.assertRaisesRegex(RelationError,'canonical rows'):
            generate.generate_full(self.captures,self.roles,extractions)


if __name__=='__main__':unittest.main()
