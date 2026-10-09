"""Source-role rejection controls, not Lean or runtime negative controls."""
import copy
import re
import unittest
from circuits.generate_transfer_epk_shared_canonical import generate
from circuits.transfer_relation import RelationError


def fixture(scope):
    private, terminal = {1: (6334, 99447), 2: (11611, 140304),
                         3: (13629, 152378), 4: (14891, 159671), 5: (16153, 166964)}[scope]
    public = {1: (6326, 6327), 2: (8515, 8516), 3: (8520, 8521),
              4: (8526, 8527), 5: (8531, 8532)}[scope]
    entries = [[0, 0], [200692, 200692], [4930, private],
               [4922, public[0]], [4923, public[1]], [89120, terminal]]
    entries += [[4931+i, private+1+i] for i in range(252)]
    return dict(scope_id=scope, restricted_map=entries,
                target_writes=[*public, *range(private+1, private+253), terminal])


class SharedCanonicalSourceTests(unittest.TestCase):
    def test_five_scopes_use_arbitrary_canonical_rows(self):
        for scope in range(1, 6):
            name, source = generate(fixture(scope))
            self.assertEqual(name, f'RuntimeTransferEpk{scope}SharedCanonical')
            checks = re.findall(r'^#check @([\w.]+)$', source, re.M)
            self.assertEqual(checks, ['bit_agreement', 'terminal_agreement', 'preserves_shared_rows'])
            self.assertEqual(checks, re.findall(r'^#print axioms ([\w.]+)$', source, re.M))
            self.assertIn('RowRenaming.satisfied_rows', source)
            self.assertIn('TransferEpkSharedCanonical.bit_agreement', source)
            self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')

    def test_wrong_terminal_or_missing_shared_write_is_refused(self):
        for kind in ('terminal', 'last_bit', 'write'):
            pair = fixture(2)
            if kind == 'terminal':
                pair['restricted_map'][5][1] += 1
            elif kind == 'last_bit':
                pair['restricted_map'][-1][1] += 1000
            else:
                pair['target_writes'].remove(11612)
            with self.subTest(kind=kind), self.assertRaises(RelationError):
                generate(pair)

    def test_boolean_or_noninjective_map_is_refused(self):
        for kind in ('boolean', 'duplicate_source', 'duplicate_target', 'scope'):
            pair = copy.deepcopy(fixture(1))
            if kind == 'boolean':
                pair['restricted_map'][0][1] = False
            elif kind == 'duplicate_source':
                pair['restricted_map'].append([4931, 999])
            elif kind == 'duplicate_target':
                pair['restricted_map'].append([999, 6335])
            else:
                pair['scope_id'] = True
            with self.subTest(kind=kind), self.assertRaises(RelationError):
                generate(pair)
