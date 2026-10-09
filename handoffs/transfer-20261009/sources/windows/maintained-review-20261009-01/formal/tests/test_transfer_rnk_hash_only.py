"""Renderer fixtures only; mocked selections supply no runtime or proof credit."""
import hashlib
import json
import re
import unittest
from unittest.mock import patch
from circuits import transfer_rnk_hash as h
from circuits import generate_transfer_rnk_hash_meaning as meaning
from tests.test_transfer_rnk_hash import fixture


class HashOnlyRendererTests(unittest.TestCase):
    def render(self, **kwargs):
        obj, handles, bindings = fixture()
        data = (json.dumps(obj)+'\n').encode()
        with patch.object(h, 'row_permutation_selection', return_value=None) as checked:
            result = h.generate_sponge_join(data, {}, None, 'a'*64, handles, bindings, **kwargs)
            self.assertEqual([call.args[2] for call in checked.call_args_list], [0,1,2])
        return result

    def test_default_bytes_preserved(self):
        source = self.render()
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
            '11a397f7b72d0ecb2b7e337aa3a38eb14d23aa36ac581a2c9b65458d42775f57')
        self.assertEqual(source, self.render(include_selection=True))

    def test_hash_only_retains_three_absorptions_and_two_audits(self):
        source = self.render(include_selection=False)
        self.assertIn('namespace ShielddSecurity.RuntimeRnkHashOnly', source)
        self.assertNotIn('RuntimeRnkSelection', source)
        self.assertNotIn('actual_regulated_branches', source)
        self.assertEqual(source.count('.permutation_sound rho one'), 3)
        self.assertEqual(source.count('private theorem '), 3)
        names = re.findall(r'^#check @(\w+)', source, re.M)
        self.assertEqual(names, ['actual_rnk_hash', 'actual_rnk_commitment'])
        self.assertEqual(names, re.findall(r'^#print axioms (\w+)', source, re.M))
        self.assertIn('permutation2_0.rawRows ++ []', source)

    def test_hash_only_keeps_actual_row_acceptance(self):
        obj, handles, bindings = fixture()
        with patch.object(h, 'row_permutation_selection', side_effect=h.relation.RelationError('actual row refusal')):
            with self.assertRaisesRegex(h.relation.RelationError, 'actual row refusal'):
                h.generate_sponge_join((json.dumps(obj)+'\n').encode(), {}, None,
                    'a'*64, handles, bindings, include_selection=False)

    def test_nonboolean_mode_refused(self):
        for value in (0,1,None,'false',[]):
            with self.assertRaisesRegex(h.relation.RelationError, 'must be Boolean'):
                h.generate_sponge_join(b'', {}, None, 'a'*64, [], {}, include_selection=value)

    def test_meaning_consumer_derives_rows_from_constructors(self):
        name, source = meaning.generate()
        self.assertEqual(name, 'RuntimeRnkHashMeaningCompletion')
        self.assertNotIn('satisfied :', source)
        self.assertNotIn('registered', source)
        self.assertNotIn('permutation_sound', source)
        self.assertIn('have done := RuntimeRnkHashSequenceCompletion.complete_rows base linked', source)
        self.assertNotRegex(source,r'namespace\s+\w+\s*:=')
        self.assertIn('18 [Poseidon.hash6', source)
        self.assertEqual(len(re.findall(r'^#check @', source, re.M)), 4)


if __name__ == '__main__': unittest.main()
