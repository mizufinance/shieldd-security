"""Small independent width3 recovery cone; compact sources remain unkernelled."""
import copy
import io
import tempfile
import unittest
from pathlib import Path
from circuits import transfer_recovery_hash as hashes, transfer_relation as relation
from circuits import transfer_note_hash_renaming as renaming
from circuits.transfer_note_t4_pages import encoded
from tests.recovery_hash_fixture import fixture


class CompactHashContextTests(unittest.TestCase):
    def test_full_typed_recovery_context_has18_bounded_modules_and205_audits(self):
        page, recovery, output, caller, artifact, rows, _, _ = fixture('secret')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root/'poseidon381.json').write_bytes(encoded(artifact))
            extracted = hashes.extract(page, io.BytesIO(rows), recovery, output, caller, root)
            selected = hashes.round_selection(page, extracted, recovery, output, caller, root)
            checked = hashes.inspect_metadata(page, recovery, output, caller, root)
            context = selected, checked, dict(metadata={}, readonly_lcs=list(caller['observed'].values()))
            template = renaming.generate_template_context(context, 'AcceptedSecretTemplate')
            self.assertEqual(len(template), 15)
            self.assertEqual(template[0][0], 'AcceptedSecretTemplate_Data')
            self.assertEqual(sum(source.count('#print axioms') for _, source in template), 133)
            modules = list(renaming.generate_compact_sound_context(context, context, 'AcceptedSecretTemplate', 'ActualSecretPage'))
            self.assertEqual(len(modules), 18)
            self.assertEqual(sum(source.count('#check @') for _, source in modules), 205)
            self.assertEqual(sum(source.count('#print axioms') for _, source in modules), 205)
            self.assertTrue(all('_Data' not in name for name, _ in modules))
            self.assertIn('Poseidon.rounds_chain', modules[-1][1])
            self.assertIn('namespace ShielddSecurity.ActualSecretPage_Compact', modules[-1][1])
            self.assertIn('AcceptedSecretTemplate_Rounds_60_64', modules[-2][1])
            changed = copy.deepcopy(context); changed[0]['calls'][0]['parameters']['ark'][5][0] += 1
            with self.assertRaises(relation.RelationError):
                list(renaming.generate_compact_sound_context(context, changed, 'AcceptedSecretTemplate', 'ActualSecretPage'))
            changed = copy.deepcopy(context)
            changed[0]['calls'][0]['segments'][7]['after'][0] = ((3, 2),)
            with self.assertRaises(relation.RelationError):
                list(renaming.generate_compact_sound_context(context, changed, 'AcceptedSecretTemplate', 'ActualSecretPage'))
            for name in ('Bad.Name', 'Bad; import False', 'é'):
                with self.assertRaises(relation.RelationError):
                    list(renaming.generate_compact_sound_context(context, context, name, 'ActualSecretPage'))


if __name__ == '__main__': unittest.main()
