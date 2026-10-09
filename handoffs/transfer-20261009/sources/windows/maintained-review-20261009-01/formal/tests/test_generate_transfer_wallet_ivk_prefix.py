"""Typed renderer fixtures/refusals only; no observation or Lean proof credit."""
import copy
import re
import unittest
from unittest.mock import patch
from circuits import generate_transfer_wallet_ivk_prefix as generator
from circuits.transfer_relation import RelationError


class WalletPrefixRendererTests(unittest.TestCase):
    def fixture(self):
        caller=dict(nk={'source':[1,1990]},ak=[{'source':[1,1977]},{'source':[1,1978]}])
        return dict(metadata=dict(caller=caller,constant_copy=200692),
            observed={(1,1990):((1993,1),),(1,1977):((1980,1),),(1,1978):((1981,1),)},
            metadata_sha256='a'*64)

    def test_six_finite_native_wallet_consumers_no_row_or_scalar_premise(self):
        with patch.object(generator.roles,'inspect_metadata',return_value=self.fixture()):
            name,source=generator.generate(b'', 'b'*64, {}, {'handles':[]})
        self.assertEqual(name,'RuntimeTransferWalletIvkPrefix')
        exports=re.findall(r'^#check @(\w+)',source,re.M)
        self.assertEqual(exports,['captured_inputs','wallet_columns','original_rows_complete',
            'wallet_scalar_value','wallet_scalar_integer','wallet_scalar_reader'])
        self.assertNotIn('(accepted :',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('(scalar :',source)
        self.assertIn('(constructed : ShielddNativeWalletAssociation.fromComponents',source)
        self.assertIn('wallet.scalar base one linked',source)
        self.assertIn('RuntimeTransferIvkKeyPrefixOwned.original_rows_complete',source)
        self.assertNotRegex(source,r'namespace\s+\w+\s*:=')
        self.assertNotIn('registered',source)

    def test_wrong_lc_and_copy_refused(self):
        for change in ('lc','copy'):
            checked=self.fixture()
            if change=='lc': checked['observed'][(1,1990)]=((1994,1),)
            else: checked['metadata']['constant_copy']=200693
            with patch.object(generator.roles,'inspect_metadata',return_value=checked):
                with self.assertRaises(RelationError):
                    generator.generate(b'', 'b'*64, {}, {'handles':[]})

    def test_acceptance_required_and_typed_failure_closed(self):
        with patch.object(generator.roles,'inspect_metadata',side_effect=RelationError('actual capture refusal')):
            with self.assertRaisesRegex(RelationError,'actual capture refusal'):
                generator.generate(b'', 'b'*64, {}, {'handles':[]})
        with self.assertRaisesRegex(RelationError,'typed accepted'):
            generator.generate(b'', 'b'*64, {}, None)


if __name__ == '__main__':unittest.main()
