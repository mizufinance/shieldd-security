"""Native source transport consumes the constructed actual cofactor output."""
import io,re,unittest
from circuits import transfer_asset_map as maps,transfer_asset_map_native_source as native
from tests.test_asset_asserted_squares import deferred_fixture


class NativeSourceTests(unittest.TestCase):
    def test_constructed_actual_output_uses_global_program_and_byte_contract(self):
        data,caller,raw,_=deferred_fixture();extracted=maps.extract(data,io.BytesIO(raw),caller)
        name,source=native.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapNativeSource')
        self.assertEqual(source.count('#check @'),4)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        self.assertIn('NativeCompletion.native_cofactor',source)
        self.assertIn('ElligatorNativeProgram.source_defined',source)
        self.assertIn('GroupByteCodec.BEWrite codec',source)
        self.assertIn('field_odd (F := F)',source)
        self.assertNotIn('field_odd cardinality',source)
        for theorem in ('native_program','actual_native_program','encoded_native_root'):
            declaration=source[source.index('theorem '+theorem):].split(':=',1)[0]
            for forbidden in ('(satisfied','(expectedRoot','(nativeSquare','(nativeParity','(nativePoint','(nonidentity'):
                self.assertNotIn(forbidden,declaration)


if __name__=='__main__':unittest.main()
