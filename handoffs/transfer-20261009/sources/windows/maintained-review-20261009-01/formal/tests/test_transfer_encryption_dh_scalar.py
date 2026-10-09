"""Synthetic scalar-source joins/theorem boundaries; no kernel/runtime credit."""
import copy
import unittest
from circuits import generate_transfer_encryption_dh_scalar as renderer
from circuits import transfer_encryption_dh as dh, transfer_epk_fixed as epk
from circuits.transfer_relation import RelationError
from tests.test_transfer_encryption_dh import fixture, encoded
from tests.test_transfer_epk_all_fixed import all_fixture


def fixture_pair(role):
    parent, raw, capsules, caller = all_fixture()
    caller['metadata'].pop('repeated_observations_equal')
    caller['metadata'].update(schema='shieldd-transfer-authorization-roles-v1', family='transfer')
    accepted = epk.inspect_all_pages(encoded(parent), raw, capsules, caller)
    slot = 0 if role == 0 else role - 1
    first = accepted['scopes'][2 + slot]['chunks'][0]['metadata']
    chunks = []
    for ordinal in range(8):
        obj = fixture(16 * ordinal, min(16, 126 - 16 * ordinal), role, True)
        obj.update({key: parent[key] for key in dh.IDENTITY})
        obj['scalar'], obj['bits'] = first['randomizer'], first['bits']
        obj['window_bits'] = [obj['bits'][2 * (125 - obj['window_start'] - offset):
                                         2 * (126 - obj['window_start'] - offset)]
                              for offset in range(obj['window_count'])]
        handles = sorted({tuple(value) for value in obj['bits']} | {tuple(obj['scalar']['source']), (1, 501)})
        obj['expressions'] = [dict(source=list(handle), terms=[[handle[1] + 3, f'{1:064x}']])
                              for handle in handles]
        chunks.append(dh.inspect_qualified_metadata(encoded(obj), parent['relation_digest'], role))
    return dh.inspect_chunks(chunks), accepted


class EncryptionDhScalarRendererTests(unittest.TestCase):
    def test_five_dh_roles_reuse_the_four_actual_epk_scope_names(self):
        for role in range(5):
            full, accepted = fixture_pair(role)
            name, text = renderer.generate(full, accepted)
            scope = 2 if role == 0 else role + 1
            self.assertEqual(name, f'RuntimeTransferEncryptionDh{role}Scalar')
            self.assertIn(f'import ShielddSecurity.TransferEpkScope{scope}Relation', text)
            self.assertIn('RuntimeTransferEpk0Canonical.bits.map', text)
            self.assertIn('EncryptionDhScalar.scalar_agrees', text)
            self.assertIn('#check @actual_scalar_multiplication', text)
            self.assertNotIn(f'RuntimeTransferEpk{scope}Canonical', text)

    def test_bounds_and_private_input_are_conclusions_of_epk_row_satisfaction(self):
        full, accepted = fixture_pair(0)
        _, text = renderer.generate(full, accepted)
        signature = text.split('theorem actual_scalar_multiplication', 1)[1].split(':= by', 1)[0]
        premises, conclusion = signature.rsplit(' :\n', 1)
        self.assertIn('epkSatisfied : Satisfies rho TransferEpkScope2Relation.rows', premises)
        self.assertIn('dhSatisfied : Satisfies rho RuntimeTransferEncryptionDh0Loop.rawRows', premises)
        self.assertNotIn('scalarRole', premises)
        self.assertNotIn('scalarBound', premises)
        self.assertIn('0 < TransferEpkScope2Relation.scalar rho', conclusion)
        self.assertIn('Scalar.order', conclusion)
        self.assertIn('eval rho privateValue', conclusion)
        self.assertIn('TransferEpkScope2Relation.sound', text)

    def test_foreign_scalar_bit_and_unqualified_occurrence_are_refused(self):
        full, accepted = fixture_pair(1)
        for change in ('scalar', 'bits', 'qualification', 'lc'):
            changed = copy.deepcopy(accepted)
            page = changed['scopes'][2]['chunks'][0]
            if change == 'scalar': page['metadata']['randomizer'] = {'source': [1, 999]}
            elif change == 'bits': page['metadata']['bits'][0] = [1, 998]
            elif change == 'qualification': changed['parent']['ordinary_full_ordered_rows_equal'] = False
            else: changed['observed'][tuple(page['metadata']['randomizer']['source'])] = ((999, 1),)
            with self.subTest(change=change), self.assertRaises(RelationError):
                renderer.generate(full, changed)
