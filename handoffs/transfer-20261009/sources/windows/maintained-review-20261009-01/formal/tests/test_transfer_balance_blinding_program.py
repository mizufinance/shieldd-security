"""Source and strict refusal only; actual126 candidates/captures are UNRUN."""
import importlib.util,inspect,unittest
from pathlib import Path
from circuits import transfer_balance_blinding_program as program, transfer_relation as relation


class BlindingProgramTests(unittest.TestCase):
    def test_unqualified_union_and_boolean_count_refuse(self):
        for extracted in ({},dict(fixed={},canonical={},parent_sha256='0'*64,
                raw_page_sha256=[],ordinary_replays=True,scope='untrusted')):
            with self.assertRaises(relation.RelationError): program.plan(b'{}\n',[],[],{},extracted)
        with self.assertRaises(relation.RelationError): program.generate(b'{}\n',[],[],{},{},include_local=1)
        with self.assertRaises(relation.RelationError): program.generate(b'{}\n',[],[],{},{},include_native_scalar=1)
        with self.assertRaises(relation.RelationError): program.generate(b'{}\n',[],[],{},{},include_native_scalar=True)

    def test_h_native_endpoint_comes_from_own_constructed_rows_and_bits(self):
        source=program.native_scalar_source()
        self.assertEqual(source.count('#print axioms'),2)
        self.assertEqual(source.count('set_option pp.all true in'),2)
        self.assertIn('RuntimeBalanceBlindingFixedCompletion.actual_rows_complete',source)
        self.assertIn('RuntimeBalanceBlindingCanonicalCompletion.constructs',source)
        self.assertIn('rw [decoded_preserved base n,integer] at coordinates',source)
        self.assertIn('valueBlindingRole',source)
        self.assertNotIn('0 < n',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('(contributionRole :',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b|^namespace \w+ :=')
        self.assertFalse(inspect.signature(program.generate).parameters['include_native_scalar'].default)

    def test_previous_default_frame_source_is_byte_identical(self):
        path=Path('.work/diagnostics/transfer-implementation-20261002/balance-variable-native-source-02/source/circuits/transfer_balance_blinding_program.py')
        if not path.exists():self.skipTest('retained previous authored source unavailable')
        spec=importlib.util.spec_from_file_location('circuits._before_h_native_scalar',path)
        before=importlib.util.module_from_spec(spec);spec.loader.exec_module(before)
        self.assertEqual(before.frame_source(300),program.frame_source(300))

    def test_universal_frame_has_exact_writes_without_row_or_endpoint_premises(self):
        source=program.frame_source(300)
        self.assertIn("List.range' 300 252",source)
        self.assertIn('program.stages.flatMap GroupCircuitCompletion.Step.writes',source)
        self.assertEqual(source.count('#print axioms'),3)
        self.assertEqual(source.count('set_option pp.all true in'),3)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide|Satisfies|nonidentity|inverse)\b')
        self.assertNotIn('0 < n',source)
        self.assertNotRegex(source,r'\b(?:have|let|intro) (?:protected|local)\b|^namespace \w+ :=')
        self.assertIn('[column] preserved column (List.mem_singleton_self column)',source)
        for invalid in (True,0,262144):
            with self.assertRaises(relation.RelationError): program.frame_source(invalid)

    def test_blinding_parameter_description_does_not_claim_spend_auth_or_entropy(self):
        source=program._description('header\n-- Native/source boundary at shieldd.lock\noldSpendAuth\n'
            'def modulus : Nat := 1\n(valueBlinding : J)\nspendAuthRole spendAuth\n')
        self.assertIn('VALUE_BLINDING',source)
        self.assertIn('canonical_bits(blinding)/multiply_fixed',source)
        self.assertIn('Canonical scalarzero',source)
        self.assertNotIn('spendAuth',source)
        self.assertNotIn('oldSpendAuth',source)
        self.assertNotIn('entropy',source)
        with self.assertRaises(relation.RelationError): program._description('unexpected source')
