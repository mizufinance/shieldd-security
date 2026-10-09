"""Tiny producer refusal controls; synthetic source data is not runtime evidence."""
import copy
import unittest

from circuits import generate_transfer_native_registered_seed as producer
from circuits.transfer_relation import RelationError
from tests.test_transfer_authorization_join import fixture


class NativeRegisteredSeedTests(unittest.TestCase):
    def test_current_typed_aliases_and_source_field(self):
        checked, ring, registry = fixture()
        name, source = producer.generate(checked, ring, registry)
        self.assertEqual(name, 'RuntimeNativeRegisteredSeed')
        self.assertIn('ShielddNativeActionWitnessAssociation.sourceSeed fq 1528 10 source base', source)
        self.assertNotRegex(source, r'namespace\s+\w+\s*:=')
        self.assertNotRegex(source, r'\bA\.')
        self.assertIn('fq.integer source.sender.registered', source)
        self.assertEqual(source.count('#print axioms '), 4)
        self.assertNotIn('Satisfies', source)

    def test_changed_registered_lc_refused(self):
        checked, ring, registry = fixture()
        ref = checked['metadata']['caller']['registered_rnk']
        expression = next(e for e in checked['metadata']['expressions'] if e['source'] == ref['source'])
        expression['terms'][0][1] = f'{2:064x}'
        checked['observed'][tuple(ref['source'])] = ((1528, 2),)
        with self.assertRaises(RelationError):
            producer.generate(checked, ring, registry)

    def test_aliased_registered_source_refused(self):
        checked, ring, registry = fixture()
        changed = copy.deepcopy(checked['metadata']['caller']['regulated'])
        checked['metadata']['caller']['registered_rnk'] = changed
        checked['metadata']['rnk_bindings']['registered'] = changed
        with self.assertRaises(RelationError):
            producer.generate(checked, ring, registry)

    def test_incompatible_ring_identity_refused(self):
        checked, ring, registry = fixture()
        ring['identity']['relation_digest'] = '0' * 64
        with self.assertRaises(RelationError):
            producer.generate(checked, ring, registry)

    def test_incompatible_registry_lc_refused(self):
        checked, ring, registry = fixture()
        with self.assertRaises(RelationError):
            producer.generate(checked, ring, [[(24, 1)], [(23, 1)]])


if __name__ == '__main__':
    unittest.main()
