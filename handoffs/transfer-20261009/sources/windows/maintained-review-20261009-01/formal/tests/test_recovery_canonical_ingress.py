"""Optional scopes and one-pass dispatch; parent acceptance tested separately."""
import io
import unittest
from unittest.mock import patch
from integration import transfer_t4_actual_ingress as ingress
from circuits import transfer_relation as relation
from tests.test_transfer_recovery_canonical import fixture


class RecoveryCanonicalIngressTests(unittest.TestCase):
    def test_existing_counts_and_optional_one_pass_pair(self):
        self.assertEqual(len(ingress.tasks()), 136)
        self.assertEqual(len(ingress.tasks_with_recovery_ranges()), 138)
        self.assertEqual(len(ingress.tasks_with_recovery_canonical()), 140)
        data, output, caller, raw = fixture()
        context = dict(prefix=dict(parent_metadata_sha256='a'*64),
                       roles=dict(original_pending_sha256='b'*64, output_data=output),
                       recovery_pending_sha256='c'*64, recovery_data=data, map_view=None)
        source = io.BytesIO(raw)
        with patch.object(ingress, 'prepare_parents', return_value=context):
            receipt = ingress.replay_recovery_canonical(b'parent', b'64', b'73', source, caller)
            self.assertEqual(source.tell(), len(raw))
            self.assertEqual(len(receipt['extraction']['slots']), 2)
            modules = list(ingress.generate_recovery_canonical(b'parent', b'64', b'73', caller, receipt))
            self.assertEqual([name for name, _ in modules], ['RuntimeTransferRecovery0Canonical','RuntimeTransferRecovery1Canonical'])
            self.assertEqual(sum(text.count('#check @') for _, text in modules), 14)
            receipt['parent_sha256']['actual74'] = 'd'*64
            with self.assertRaisesRegex(relation.RelationError, 'receipt identity'):
                list(ingress.generate_recovery_canonical(b'parent', b'64', b'73', caller, receipt))


if __name__ == '__main__': unittest.main()
