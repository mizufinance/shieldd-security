import unittest
from pathlib import Path
from unittest.mock import patch

from circuits import generate_transfer_ownership_native_address as generator
from circuits.transfer_relation import RelationError


class NativeAddressTests(unittest.TestCase):
    def render(self, inputs=(((1504,1),),((1505,1),))):
        cones=dict(cones=[dict(role='formula0',inputs=['x','y'])],
            observations=dict(x=('source',inputs[0]),y=('source',inputs[1])))
        with patch.object(generator.endpoint,'generate'), \
             patch.object(generator.endpoint,'endpoint_plan',return_value=dict(columns=[1512,1513],constant_copy=200692)), \
             patch.object(generator.endpoint.scalar.native.tables.completion.owner,'cone_certificates',return_value=cones):
            return generator.generate([{}],[{}],b'ivk',{},b'reduction',{},'params','a'*64)

    def test_same_ivk_secret_and_native_address_guard_derive_actual_roles(self):
        name,source=self.render()
        self.assertEqual(name,'RuntimeOwnershipNativeAddress')
        self.assertEqual(source.count('#check @'),4)
        self.assertEqual(source.count('#print axioms'),4)
        self.assertIn('ShielddNativeAddress.secret_from_ivk primitives _ scalar accepted',source)
        self.assertIn('ShielddNativeAddress.viewsAddress',source)
        self.assertIn('ShielddNativeAddress.paymentAddress',source)
        self.assertIn('RuntimeOwnershipNativeEndpoint.prefix_windows_endpoint_complete',source)
        self.assertIn('RuntimeOwnershipNativeEndpoint.completed_targets',source)
        self.assertIn('eval built [(1504,1)]',source)
        self.assertIn('eval built [(1512,1)]',source)
        self.assertNotIn('transfer_public_private',source)
        self.assertNotIn('target_role',source)
        for mode in ('viewed','payment'):
            statement=source.split('theorem '+mode+'_address_complete',1)[1].split(' := by',1)[0]
            self.assertEqual(statement.count('Satisfies'),1)
            self.assertNotIn('desired',statement)
            self.assertNotIn('sameTransmission',statement)

    def test_non_singleton_original_diversified_input_refuses(self):
        with self.assertRaises(RelationError):self.render((((1504,1),(1505,1)),((1505,1),)))

    def test_endpoint_must_first_pass_typed_acceptance(self):
        with patch.object(generator.endpoint,'generate',side_effect=RelationError('actual endpoint missing')):
            with self.assertRaises(RelationError):generator.generate([],[],b'',{},b'',{},'params','a'*64)

    def test_owned_address_program_and_named_global_contract_scope(self):
        text=(Path(__file__).resolve().parents[1]/'circuits/ShielddSecurity/ShielddNativeAddress.lean').read_text()
        self.assertIn('primitives.aes128 key (indexBytes index)',text)
        self.assertIn('primitives.blake2b personalization diversifier',text)
        self.assertIn('if upstream.isIdentity point then none else some',text)
        self.assertIn('decide (key = address.transmission)',text)
        self.assertIn('parseCanonical : ∀ scalar',text)
        self.assertIn('promoteMultiply : ∀ point scalar',text)
        self.assertEqual(text.count('#check @'),7)
        self.assertEqual(bytes([83,104,105,101,108,100,100,95,68,105,118,114,115,102,121]),b'Shieldd_Divrsfy')


if __name__=='__main__':unittest.main()
