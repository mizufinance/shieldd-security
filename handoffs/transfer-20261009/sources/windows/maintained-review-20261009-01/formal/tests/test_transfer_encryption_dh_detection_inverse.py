"""Full-digest synthetic selected-key inverse rows; no native/kernel credit."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_encryption_dh_detection_inverse as inverse
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests.test_transfer_encryption_dh_keys import fixture as keys


def fixture(change=None):
    checked = keys()
    for handle, (multiply, left, right) in sorted(checked['nodes'].items()):
        a, b = checked['derived'][left], checked['derived'][right]
        checked['derived'][handle] = ((200 + handle[1], 1),) if multiply else combine(a, b)
    x = checked['derived'][checked['bindings']['detection_key'][0][1]]
    copy_column, domain = 3500, 4096
    rows = [(canonical([(0, 1), (copy_column, -1)]), ())]
    for q, aux, product in [(2000, 2001, 2002)] + ([(2010, 2011, 2012)] if change == 'ambiguous' else []):
        rows.extend([(combine(((q, 1),), x, -1), ((aux, 1),)),
                     (combine(((q, 1),), x), canonical([(aux, 1), (product, 4)])),
                     (canonical([(product, 1), (0, -1)]), ())])
    if change == 'missing':
        rows[2] = ((), ())
    elif change == 'assertion':
        rows[3] = (canonical([(2002, 1), (0, -2)]), ())
    elif change == 'reversed':
        rows[1] = (canonical((c, -v) for c, v in rows[1][0]), rows[1][1])
    elif change == 'duplicate_copy':
        rows.append(rows[0])
    elif change == 'decoys':
        rows.extend((combine(((2100 + i, 1),), x, -1), ((2200 + i, 1),)) for i in range(65))
    elif change == 'bound':
        for i in range(65):
            q, aux, product = 2100 + i, 2200 + i, 2300 + i
            rows.extend([(combine(((q, 1),), x, -1), ((aux, 1),)),
                         (combine(((q, 1),), x), canonical([(aux, 1), (product, 4)])),
                         (canonical([(product, 1), (0, -1)]), ())])
    outline = lambda lc: canonical((copy_column if c == 0 else c, v) for c, v in lc)
    encode = lambda lc: [[c, f'{v:064x}'] for c, v in canonical(lc)]
    records = [dict(row=i, a=encode(a if i == 0 or change == 'duplicate_copy' and i == len(rows)-1 else outline(a)),
                    b=encode(b if i == 0 else outline(b))) for i, (a, b) in enumerate(rows)]
    public, blocks = [[1, 100]], [[[1, 101]]]
    digest = blake3(relation.NAMESPACE + relation.u64(domain) + relation.u64(len(records)) +
                    relation.indices(public) + relation.u64(1) + relation.indices(blocks[0]))
    for row in records:
        digest.update(b'A' + relation.terms(row['a'], domain) + b'B' + relation.terms(row['b'], domain))
    identity = digest.hexdigest()
    header = dict(schema='shieldd-transfer-relation-v1', family='transfer', relation_digest=identity,
                  domain_size=domain, stored_rows=len(records), public_inputs=1, committed_blocks=[1],
                  constant_column=0, public_columns=[1], committed_columns=[[2]], source_public=public,
                  source_blocks=blocks, coefficient_encoding='canonical-big-endian-32',
                  field_modulus=str(relation.MODULUS),
                  role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                  padding='implicit-all-zero-rows-to-domain-size')
    data = b''.join(json.dumps(item).encode() + b'\n' for item in [header, *records, dict(eof=True, rows=len(records))])
    checked.update(metadata=dict(schema='shieldd-transfer-encryption-dh-v1', role=0,
        relation_digest=identity, domain_size=domain, full_rows=len(records), constant_copy=copy_column),
        metadata_sha256='a' * 64)
    return checked, data


class EncryptionDhDetectionInverseTests(unittest.TestCase):
    def test_three_complete_replays_match_actual_fused_key_lc_and_all_four_rows(self):
        for change in (None, 'reversed', 'decoys'):
            checked, data = fixture(change)
            opened = []
            def stream():
                opened.append(True)
                return io.BytesIO(data)
            result = inverse.extract(checked, stream)
            self.assertEqual(len(opened), 3)
            self.assertEqual(len(result['selected_rows']), 4)
            self.assertEqual(result['certificate']['quotient'], ((2000, 1),))
            name, source = inverse.generate(checked, result)
            self.assertEqual(name, 'RuntimeTransferEncryptionDetectionInverse')
            self.assertIn('#check @represented_nonidentity', source)
            self.assertIn('Compiler.checked_product_sound', source)
            self.assertIn('model.coordinates represented = point rho', source)
            self.assertNotIn('honest', source)
            signature = source.split('theorem x_nonzero', 1)[1].split(':= by', 1)[0]
            self.assertNotIn('(nonzero', signature)
            self.assertIn('satisfied : Satisfies rho rawRows', signature)

    def test_missing_wrong_assertion_ambiguous_copy_and_candidate_overflow_refused(self):
        for change in ('missing', 'assertion', 'ambiguous', 'duplicate_copy', 'bound'):
            checked, data = fixture(change)
            with self.subTest(change=change), self.assertRaises(relation.RelationError):
                inverse.extract(checked, lambda: io.BytesIO(data))

    def test_changed_row_point_identity_and_pending_capture_refused(self):
        checked, data = fixture()
        result = inverse.extract(checked, lambda: io.BytesIO(data))
        for change in ('row', 'point', 'metadata', 'relation'):
            bad = copy.deepcopy(result)
            if change == 'row':
                bad['selected_rows'][2]['b'][-1][1] = f'{7:064x}'
            elif change == 'point':
                bad['point'] = (((99, 1),), bad['point'][1])
            elif change == 'metadata':
                bad['metadata_sha256'] = 'b' * 64
            else:
                bad['identity']['relation_digest'] = 'b' * 64
            with self.subTest(change=change), self.assertRaises(relation.RelationError):
                inverse.generate(checked, bad)
        checked['qualified'] = False
        def forbidden():
            self.fail('pending observer reached full replay')
        with self.assertRaises(relation.RelationError):
            inverse.extract(checked, forbidden)
