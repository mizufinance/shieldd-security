"""Owned source-wiring mutation controls; no native/crypto result credit."""
import copy
import json
from pathlib import Path
import unittest

from circuits.statement_projection import native_source_arguments


FIXTURE = Path(__file__).parent / 'fixtures/transfer_native_source_arguments.json'


def fixture():
    packet = json.loads(FIXTURE.read_text())
    assert packet['scope'] == 'selected function token fixtures only; not compiled runtime source'
    return packet['sources']


class NativeSourceBindingsTests(unittest.TestCase):
    def test_current_reviewed_constructor_arguments_without_qualification(self):
        result = native_source_arguments(fixture())
        self.assertEqual(result['contexts'], {'Ordinary': 1, 'FeeFunding': 2})
        self.assertEqual(len(result['full64_order']), 64)
        self.assertEqual(dict(result['retained_action_constructor'])['anchor'], 'context.anchor')
        self.assertIn('nonidentity', dict(result['public_constructor'])['rk'])
        self.assertEqual(result['gates'], 'OPEN')
        self.assertEqual(result['evidence'], [])
        self.assertFalse(result['native_run'])
        self.assertFalse(result['kernel_run'])

    def mutate(self, suffix, before, after, marker):
        sources = copy.deepcopy(fixture())
        path = next(path for path in sources if path.endswith(suffix))
        self.assertEqual(sources[path].count(before), 1)
        sources[path] = sources[path].replace(before, after)
        with self.assertRaisesRegex(ValueError, marker):
            native_source_arguments(sources)

    def test_fee_context_two_cannot_be_zero(self):
        self.mutate('volume_accumulator.rs', 'FeeFunding => 2u64', 'FeeFunding => 0u64', 'volume::as_field')

    def test_outer_anchor_cannot_be_replaced_by_body_or_asset(self):
        self.mutate('action_handler/transfer.rs', 'anchor : context . anchor',
                    'anchor : transfer . body . anchor', 'retained action/public source')
        self.mutate('public_input_hash.rs', 'anchor : p . anchor',
                    'anchor : p . asset_anchor', 'statement argument binding')

    def test_rk_identity_and_coordinate_role_substitution_refused(self):
        self.mutate('public_input_hash.rs', 'encoding :: nonidentity',
                    'encoding :: point', 'statement argument binding')
        self.mutate('public_input_hash.rs', 'Point { x , y }', 'Point { x : y , y : x }', 'public::point')

    def test_field_byte_order_and_public_family_refused(self):
        self.mutate('circuits/src/encoding.rs', 'bytes . reverse ( ) ;', '', 'codec::field')
        self.mutate('transfer/proof.rs', 'Family :: Transfer ) ?', 'Family :: NoteReshape ) ?', 'proof::to_batch_item')

    def test_complete_decoder_and_key_policy_refused(self):
        self.mutate('transfer/action.rs', 'auth_sig , proof :', 'auth_sig : [ 0 ; 64 ] , proof :', 'full Transfer decoder')
        self.mutate('primitives/src/encoding.rs', 'point . to_bytes ( ) == * bytes',
                    'true', 'primitive::point')
        self.mutate('primitives/src/encoding.rs', '! bool :: from ( point . is_identity ( ) )',
                    'true', 'primitive::nonidentity')

    def test_statement_domain_and_hash_count_refused(self):
        self.mutate('public_input_hash.rs', 'domains :: TRANSFER_STATEMENT',
                    'domains :: RESHAPE_ONE_TO_EIGHT_STATEMENT', 'public::transfer_statement_hash')
        self.mutate('public_input_hash.rs', 'fields . len ( ) == count', 'true', 'public::hash')

    def test_shadowed_extra_flow_attributes_and_duplicate_function_refused(self):
        self.mutate('public_input_hash.rs', 'p . validate_shape ( ) ? ;',
                    'let p = different_public ; p . validate_shape ( ) ? ;', 'statement argument binding')
        self.mutate('public_input_hash.rs', 'fn transfer_statement(',
                    '# [ cfg ( any ( ) ) ] fn transfer_statement(', 'unsupported native function attribute')
        sources = fixture()
        path = next(path for path in sources if path.endswith('public_input_hash.rs'))
        sources[path] += '\nfn transfer_statement() { different(); }'
        with self.assertRaisesRegex(ValueError, 'ambiguous native function'):
            native_source_arguments(sources)

    def test_comment_normalization_preserves_strings_and_fails_closed(self):
        sources = fixture()
        path = next(path for path in sources if path.endswith('public_input_hash.rs'))
        sources[path] = '/* outside /* nested */ complete */\n' + sources[path]
        self.assertEqual(len(native_source_arguments(sources)['full64_order']), 64)
        self.mutate('public_input_hash.rs', '"transfer output shape"',
                    '"transfer  output shape"', 'statement argument binding')
        sources[path] = '/* unfinished'
        with self.assertRaisesRegex(ValueError, 'unterminated native source comment'):
            native_source_arguments(sources)

    def test_exact_input_set_and_string_types(self):
        sources = fixture()
        sources.pop(next(iter(sources)))
        with self.assertRaisesRegex(ValueError, 'input set'):
            native_source_arguments(sources)
        sources = fixture()
        sources[next(iter(sources))] = True
        with self.assertRaisesRegex(ValueError, 'input set'):
            native_source_arguments(sources)


if __name__ == '__main__':
    unittest.main()
