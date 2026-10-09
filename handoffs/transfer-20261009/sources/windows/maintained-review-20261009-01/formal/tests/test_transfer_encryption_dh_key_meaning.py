"""Source/LC joins using complete synthetic cofactor replay; no kernel credit."""
import copy
import io
import re
import unittest
from circuits import transfer_encryption_dh_cofactor as cofactor
from circuits import transfer_encryption_dh_cofactor_candidates as search
from circuits import generate_transfer_encryption_dh_key_meaning as meaning
from circuits.transfer_balance_rows import combine
from circuits.transfer_relation import RelationError
from tests.test_transfer_encryption_dh_cofactor_candidates import fixture


def extracted():
    checked, template, data, _ = fixture()
    # The cofactor search fixture only needs primitive source LCs. This join
    # additionally needs every observed selector product/add LC, just as the
    # typed runtime observer provides them. Allocate synthetic product columns
    # and derive each add from its actual earlier operands.
    for handle, (multiply, left, right) in sorted(checked['nodes'].items()):
        a, b = checked['derived'][left], checked['derived'][right]
        checked['derived'][handle] = (((70000 + handle[1], 1),) if multiply
                                      else combine(a, b))
    found = search.find(checked, template, lambda: io.BytesIO(data))
    return checked, cofactor.extract(checked, template, found['columns'], io.BytesIO(data))


class EncryptionDhKeyMeaningTests(unittest.TestCase):
    def test_exact_keys_join_real_cofactor_extraction_and_row_interpolation(self):
        checked, proof = extracted()
        name, source = meaning.generate(checked, proof)
        self.assertEqual(name, 'RuntimeTransferEncryptionKeyMeaning')
        checks = re.findall(r'^#check @([\w.]+)$', source, re.M)
        self.assertEqual(len(checks), 7)
        self.assertEqual(checks, re.findall(r'^#print axioms ([\w.]+)$', source, re.M))
        self.assertIn('RuntimeTransferEncryptionLeafDetectionSubgroup.actual_subgroup', source)
        self.assertIn('RuntimeTransferEncryptionPayloadKeySelection.axis1_interpolation', source)
        self.assertIn('def leafDetection', source)
        self.assertIn('eval rho [(1100, (1 : Int))]', source)
        signature = source.split('theorem represented_keys', 1)[1].split(':= by', 1)[0]
        premises, conclusion = signature.split('(satisfied : Satisfies rho rows) :', 1)
        self.assertNotIn('(leafD', premises)
        self.assertNotIn('(selectedD', premises)
        self.assertNotIn('≠ 0', conclusion)
        self.assertIn('(four : (4 : F) ≠ 0)', premises)
        self.assertIn('subgroupOrder • leafD = 0', conclusion)
        self.assertIn('model.coordinates selectedP = selectedPayload rho', conclusion)
        self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')

    def test_foreign_leaf_and_selector_source_cannot_replace_constrained_key(self):
        checked, original = extracted()
        for change in ('point', 'namespace', 'missing', 'selector'):
            proof = copy.deepcopy(original)
            if change == 'point':
                proof['cofactors'][0]['point'] = (((1101, 1),), ((1101, 1),))
            elif change == 'namespace':
                proof['cofactors'][1]['namespace'] = 'RuntimeTransferAk'
            elif change == 'missing':
                proof['cofactors'].pop()
            else:
                proof['selectors']['regulated_candidate'] = ('source', (1, 51))
            with self.subTest(change=change), self.assertRaises(RelationError):
                meaning.generate(checked, proof)
        broken = copy.deepcopy(checked)
        del broken['derived'][broken['bindings']['detection_key'][0][1]]
        with self.assertRaisesRegex(RelationError, 'missing captured source LC'):
            meaning.generate(broken, original)

    def test_unqualified_foreign_schema_or_nonfirst_occurrence_is_refused(self):
        original, proof = extracted()
        for change in ('pending', 'schema', 'role', 'bool_role'):
            checked = copy.deepcopy(original)
            if change == 'pending':
                checked['qualified'] = False
            elif change == 'schema':
                checked['metadata']['schema'] = 'shieldd-transfer-ownership-v1'
            else:
                checked['metadata']['role'] = False if change == 'bool_role' else 1
            with self.subTest(change=change), self.assertRaises(RelationError):
                meaning.generate(checked, proof)
