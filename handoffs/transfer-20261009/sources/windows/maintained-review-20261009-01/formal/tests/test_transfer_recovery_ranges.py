"""Source-bound range construction, including the explicit canonicality gap."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_recovery_ranges as ranges, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests.test_transfer_recovery_capsule import fixture as capsule_fixture
from circuits.transfer_note_t4_pages import encoded


def fixture():
    data, output_data, caller, raw = capsule_fixture()
    obj = json.loads(data); output = json.loads(output_data)
    records = [json.loads(line) for line in raw.splitlines()]
    header, rows = records[0], records[1:-1]
    for slot in (0, 1):
        selected = ranges.boundary(data, output_data, caller, slot)
        for c in selected['columns']:
            rows.append(dict(row=len(rows), a=[[c, f'{1:064x}']], b=[[c, f'{1:064x}']]))
        delta = combine(selected['weighted'], ((selected['value'], 1),), -1)
        if slot: delta = canonical((c, -v) for c, v in delta)
        rows.append(dict(row=len(rows), a=[[c, f'{v:064x}'] for c, v in delta], b=[]))
    digest = blake3()
    digest.update(relation.NAMESPACE + relation.u64(header['domain_size']) + relation.u64(len(rows)) +
                  relation.indices(header['source_public']) + relation.u64(1) + relation.indices(header['source_blocks'][0]))
    for row in rows: digest.update(b'A' + relation.terms(row['a'], header['domain_size']) + b'B' + relation.terms(row['b'], header['domain_size']))
    for owner in (obj, output, caller['metadata']): owner.update(relation_digest=digest.hexdigest(), full_rows=len(rows))
    header.update(relation_digest=digest.hexdigest(), stored_rows=len(rows))
    stream = b''.join(encoded(v) for v in [header, *rows, dict(eof=True, rows=len(rows))])
    return encoded(obj), encoded(output), caller, stream


class RecoveryRangeTests(unittest.TestCase):
    def test_exact_rows_construct_only_bits_and_explicitly_allow_noncanonical252(self):
        data, outputs, caller, raw = fixture(); modulus = relation.MODULUS
        for slot in (0, 1):
            selected = ranges.extract(data, io.BytesIO(raw), outputs, caller, slot)
            self.assertEqual(len(selected['selected_rows']), 254)
            boundary = ranges.boundary(data, outputs, caller, slot)
            for n in (0, 1, 2**252 - 1):
                base = {c: (31*c + 7) % modulus for c in range(4096)}
                base[0] = base[4000] = 1; base[boundary['value']] = n
                assignment = dict(base)
                for i, c in enumerate(boundary['columns']): assignment[c] = n >> i & 1
                ev = lambda terms: sum(assignment[c]*int(v, 16) for c, v in terms) % modulus
                self.assertTrue(all(ev(row['a'])**2 % modulus == ev(row['b']) for row in selected['selected_rows']))
                self.assertTrue(all(assignment[c] == base[c] for c in base if c not in boundary['columns']))
            source = ranges.generate(data, selected, outputs, caller, slot)
            self.assertEqual(source.count('#check @'), 5)
            self.assertEqual(source.count('#print axioms'), 5)
            self.assertIn('n < 2^252', source)
            self.assertNotIn('n < Scalar.order', source)
            self.assertIn('ORDER-1 comparator', source)
            changed = copy.deepcopy(selected); changed['selected_rows'].pop()
            with self.assertRaises(relation.RelationError): ranges.generate(data, changed, outputs, caller, slot)

    def test_order_slot_and_full_stream_refusals(self):
        data, outputs, caller, raw = fixture()
        for slot in (True, -1, 2):
            with self.assertRaises(relation.RelationError): ranges.boundary(data, outputs, caller, slot)
        for invalid in (b'\n'.join(raw.splitlines()[:-1]) + b'\n', raw + b'x'):
            with self.assertRaises(relation.RelationError): ranges.extract(data, io.BytesIO(invalid), outputs, caller, 0)
        selected = ranges.extract(data, io.BytesIO(raw), outputs, caller, 0)
        with self.assertRaises(relation.RelationError): ranges.generate(data, selected, outputs, caller, 1)


if __name__ == '__main__': unittest.main()
