import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_precompute_frame as generator
from tests.test_transfer_ownership_precompute_tables import fixture
from circuits.transfer_relation import RelationError


class PrecomputeFrameTests(unittest.TestCase):
    def test_full_seed_materialization_quotient_addition_footprint(self):
        checked, cones, _ = fixture()
        with patch.object(generator.tables,'generate',return_value=('RuntimeOwnershipWindow000NativeTables','source')), \
             patch.object(generator.tables.completion.owner,'cone_certificates',return_value=cones):
            name, source = generator.generate(checked,{})
        self.assertEqual(name,'RuntimeOwnershipWindow000PrecomputeFrame')
        self.assertEqual(source.count('#check @'),2)
        self.assertEqual(source.count('#print axioms'),2)
        self.assertIn('def writes : List Nat := [1504,1505]',source)
        self.assertIn('Point0Materializations.steps.flatMap',source)
        self.assertIn('Point0Completion.x.writes',source)
        self.assertIn('Point0Completion.y.writes',source)
        self.assertIn('NativePrecompute.writes',source)
        statement=source.split('theorem outside',1)[1].split(' := by',1)[0]
        self.assertNotIn('Satisfies',statement)
        self.assertNotIn('OnCurve',statement)
        self.assertIn('column ∉ writes',statement)
        self.assertIn('GroupCircuitOrder.run_outside',source)
        self.assertIn('ShielddPointCoordinateSeed.seed_preserves',source)

    def test_requires_existing_strict_actual_table_join(self):
        with patch.object(generator.tables,'generate',side_effect=RelationError('table mismatch')):
            with self.assertRaises(RelationError):generator.generate({}, {})


if __name__=='__main__':unittest.main()
