"""Synthetic full-digest row-search controls, without cofactor/kernel credit."""
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_encryption_dh_cofactor_candidates as candidates
from circuits import transfer_encryption_dh_cofactor as cofactor
from circuits.transfer_balance_rows import canonical
from circuits import transfer_relation as relation
from tests.test_transfer_encryption_dh_keys import fixture as key_fixture


def fixture(change=None):
    checked = key_fixture()
    replacements = {(1, 0): (1, 50), (1, 1): (1, 1097), (1, 2): (1, 1098),
                    (1, 3): (1, 1197), (1, 4): (1, 1198)}
    for field in ('expressions', 'derived'):
        checked[field] = {replacements.get(h, h): (((replacements[h][1] + 3, 1),) if h in replacements else lc)
                          for h, lc in checked[field].items()}
    checked['nodes'] = {h: (mul, replacements.get(a, a), replacements.get(b, b))
                        for h, (mul, a, b) in checked['nodes'].items()}
    copy, domain = 120000, 131072
    source = [(((1982, 1),), ((49716, 1),))]
    source.extend((canonical([(1980 + i % 7, 1), (49716 + i - 1, 2)]), ((49716 + i, 1),))
                  for i in range(1, 64))
    source.extend([(canonical([(1980, 1), (49779, -1)]), ()),
                   (canonical([(1981, 1), (49778, -1)]), ())])
    source.extend((((1986, i),), ()) for i in range(2, 6))
    source.append((canonical([(0, 1), (copy, -1)]), ()))
    assert len(source) == 71
    maps = {}
    rows = []
    for key, point, aux in [('detection_key', 1100, 60000), ('payload_key', 1200, 61000)]:
        columns = {c for row in source for lc in row for c, _ in lc}
        mapping = {c: c if c in (0, copy) else c + point - 1980 if c < 49716 else c + aux - 49716
                   for c in columns}
        maps[key] = mapping
        rows.extend(tuple(canonical((mapping[c], v) for c, v in lc) for lc in row) for row in source)
    if change == 'missing': rows[20] = ((), ())
    if change == 'ambiguous':
        mapping = {c: value + 400 if 49716 <= c <= 49779 else value for c, value in maps['detection_key'].items()}
        rows.extend(tuple(canonical((mapping[c], v) for c, v in lc) for lc in row) for row in source)
    encode = lambda terms: [[c, f'{v:064x}'] for c, v in terms]
    records = [dict(row=i, a=encode(a), b=encode(b)) for i, (a, b) in enumerate(rows)]
    public, blocks = [[1, 100001]], [[[1, 100002]]]
    digest = blake3(relation.NAMESPACE + relation.u64(domain) + relation.u64(len(records)) +
                    relation.indices(public) + relation.u64(1) + relation.indices(blocks[0]))
    for row in records:
        digest.update(b'A' + relation.terms(row['a'], domain) + b'B' + relation.terms(row['b'], domain))
    identity = digest.hexdigest()
    header = dict(schema='shieldd-transfer-relation-v1', family='transfer', relation_digest=identity,
                  domain_size=domain, stored_rows=len(records), public_inputs=1, committed_blocks=[1],
                  constant_column=0, public_columns=[1], committed_columns=[[2]],
                  source_public=public, source_blocks=blocks, coefficient_encoding='canonical-big-endian-32',
                  field_modulus=str(relation.MODULUS),
                  role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                  padding='implicit-all-zero-rows-to-domain-size')
    data = b''.join((json.dumps(value).encode() + b'\n') for value in
                    [header, *records, dict(eof=True, rows=len(records))])
    checked['metadata'] = dict(schema='shieldd-transfer-encryption-dh-v1', role=0,
                               relation_digest=identity, domain_size=domain, full_rows=len(records), constant_copy=copy)
    template = dict(identity=dict(relation_digest=identity, domain_size=domain, stored_rows=len(records)),
                    selected_rows=[dict(row=i, a=encode(a), b=encode(b)) for i, (a, b) in enumerate(source)])
    return checked, template, data, maps


class EncryptionDhCofactorCandidateTests(unittest.TestCase):
    def test_two_full_streams_cover_all_rows_then_independent_extractor_rechecks(self):
        checked, template, data, maps = fixture()
        opened = []
        def open_stream():
            opened.append(True)
            return io.BytesIO(data)
        result = candidates.find(checked, template, open_stream)
        self.assertEqual(len(opened), 2)
        self.assertEqual(result['columns'], maps)
        extracted = cofactor.extract(checked, template, result['columns'], io.BytesIO(data))
        self.assertEqual([len(item['row_pairs']) for item in extracted['cofactors']], [71, 71])
        generated = cofactor.generate(extracted)
        self.assertEqual(len(generated), 2)
        for _, text in generated:
            self.assertIn('RuntimeTransferCofactor', text)
            self.assertNotIn('actual_ak_subgroup', text)
            signature = text.split('theorem actual_subgroup', 1)[1].split(':= by', 1)[0]
            self.assertNotIn('≠ 0', signature)

    def test_one_missing_row_or_two_complete_maps_is_refused(self):
        for change in ('missing', 'ambiguous'):
            checked, template, data, _ = fixture(change)
            with self.subTest(change=change), self.assertRaisesRegex(relation.RelationError, 'one complete71-row map'):
                candidates.find(checked, template, lambda: io.BytesIO(data))

    def test_incomplete_basis_foreign_point_or_pending_occurrence_fail_before_replay(self):
        for change in ('basis', 'point', 'pending'):
            checked, template, data, _ = fixture()
            if change == 'basis': template['selected_rows'].pop()
            elif change == 'point': checked['derived'][(1, 1097)] = ((1101, 1),)
            else: checked['qualified'] = False
            def forbidden():
                self.fail('invalid source/basis reached the ordinary stream')
            with self.subTest(change=change), self.assertRaises(relation.RelationError):
                candidates.find(checked, template, forbidden)
