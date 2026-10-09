"""Unqualified comparator fixtures: exact row joins and semantic refusals."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_recovery_canonical as comparator, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests.test_transfer_recovery_ranges import fixture as range_fixture
from circuits.transfer_note_t4_pages import encoded


def fixture(duplicate=False, missing=False):
    data, outputs, caller, stream = range_fixture()
    metadata, output = json.loads(data), json.loads(outputs)
    records = [json.loads(line) for line in stream.splitlines()]
    header, rows = records[0], records[1:-1]
    columns = [comparator.ranges.boundary(data, outputs, caller, slot)['columns'] for slot in (0, 1)]
    def append(a, b):
        outline = lambda lc: canonical((4000 if c == 0 else c, v) for c, v in lc)
        rows.append(dict(row=len(rows), a=[[c, f'{v:064x}'] for c, v in outline(a)],
                         b=[[c, f'{v:064x}'] for c, v in outline(b)]))
    for slot in (0, 1):
        before = comparator.ONE
        for index, column in enumerate(columns[slot]):
            left = ((column, 1),); right = ((comparator.ORDER - 1) >> index) & 1
            both = combine(comparator.ONE, left, -1) if right else ()
            factor = combine(combine(comparator.ONE, left, -1), ((0, right),) if right else ())
            factor = combine(factor, both, -2)
            if index == 0: product = factor
            else:
                product, auxiliary = ((5000 + 600*slot + 2*index, 1),), ((5001 + 600*slot + 2*index, 1),)
                if not (missing and slot == 0 and index == 7):
                    append(combine(before, factor, -1), auxiliary)
                    if duplicate and slot == 0 and index == 7:
                        append(combine(before, factor, -1), auxiliary)
                append(combine(before, factor), combine(auxiliary, product, 4))
            before = combine(both, product)
        append(combine(before, comparator.ONE, -1), ())
    domain = 8192; digest = blake3()
    digest.update(relation.NAMESPACE + relation.u64(domain) + relation.u64(len(rows)) +
                  relation.indices(header['source_public']) + relation.u64(1) + relation.indices(header['source_blocks'][0]))
    for row in rows:
        digest.update(b'A' + relation.terms(row['a'], domain) + b'B' + relation.terms(row['b'], domain))
    for owner in (metadata, output, caller['metadata']):
        owner.update(relation_digest=digest.hexdigest(), domain_size=domain, full_rows=len(rows))
    header.update(relation_digest=digest.hexdigest(), domain_size=domain, stored_rows=len(rows))
    raw = b''.join(encoded(record) for record in [header, *rows, dict(eof=True, rows=len(rows))])
    return encoded(metadata), encoded(output), caller, raw


class RecoveryCanonicalTests(unittest.TestCase):
    def test_two_slots_single_replay_and_json_roundtrip_candidates(self):
        data, output, caller, stream = fixture()
        selected = comparator.extract(data, io.BytesIO(stream), output, caller)
        selected = json.loads(json.dumps(selected))
        self.assertEqual(len(selected['slots']), 2)
        for slot in (0, 1):
            self.assertEqual(len(selected['slots'][slot]['steps']), 252)
            self.assertEqual(len(selected['slots'][slot]['products']), 251)
            source = comparator.generate(data, selected, output, caller, slot)
            self.assertEqual(source.count('#check @'), 7)
            self.assertEqual(source.count('#print axioms'), 7)
            self.assertIn(f'namespace ShielddSecurity.RuntimeTransferRecovery{slot}Canonical', source)
            self.assertIn('r < Scalar.order', source)
            self.assertNotIn('source', selected['slots'][slot]['steps'][2])

    def test_missing_and_ambiguous_physical_pairs_refused(self):
        for options in (dict(missing=True), dict(duplicate=True)):
            data, output, caller, stream = fixture(**options)
            with self.assertRaisesRegex(relation.RelationError, 'unique product pair'):
                comparator.extract(data, io.BytesIO(stream), output, caller)

    def test_retained_endpoint_recurrence_and_slot_refusals(self):
        data, output, caller, stream = fixture()
        selected = comparator.extract(data, io.BytesIO(stream), output, caller)
        changed = copy.deepcopy(selected); changed['slots'][0]['steps'][4]['right'] ^= 1
        with self.assertRaisesRegex(relation.RelationError, 'certificate changed'):
            comparator.generate(data, changed, output, caller, 0)
        changed = copy.deepcopy(selected); changed['slots'][0]['steps'][4]['right'] = bool(changed['slots'][0]['steps'][4]['right'])
        with self.assertRaisesRegex(relation.RelationError, 'certificate changed'):
            comparator.generate(data, changed, output, caller, 0)
        changed = copy.deepcopy(selected); changed['slots'][0]['selected_rows'].pop()
        with self.assertRaises(relation.RelationError): comparator.generate(data, changed, output, caller, 0)
        with self.assertRaises(relation.RelationError): comparator.generate(data, selected, output, caller, True)
        with self.assertRaises(relation.RelationError): comparator.extract(data, io.BytesIO(stream[:-1]), output, caller)

    def test_comparator_semantics_reject_order_alias_in_252_range(self):
        data, output, caller, stream = fixture()
        selected = comparator.extract(data, io.BytesIO(stream), output, caller)['slots'][0]
        boundary = comparator.ranges.boundary(data, output, caller, 0)
        records = {row['row']: row for row in selected['selected_rows']}
        pairs = {item['step']: item['rows'] for item in selected['products']}
        endpoint = next(item['row'] for item in selected['templates'] if item['roles'] == ['endpoint'])
        for n in (0, 1, comparator.ORDER - 1, comparator.ORDER, comparator.ORDER + 1, 2**252 - 1):
            le = 1
            for index in range(252):
                left = (n >> index) & 1; right = ((comparator.ORDER - 1) >> index) & 1
                both = (1-left)*right
                le = both + le*((1-left)+right-2*both)
            self.assertEqual(le, int(n < comparator.ORDER))
            rho = {0: 1, 4000: 1, boundary['value']: n}
            for index, column in enumerate(boundary['columns']): rho[column] = (n >> index) & 1
            evaluate = lambda terms: sum(rho[c]*v for c, v in terms) % relation.MODULUS
            for index, step in enumerate(selected['steps']):
                if not index: continue
                # Fixture has materialized unit outputs and real difference
                # auxiliary rows; assigning them does not assume the endpoint.
                product_column = step['product'][0][0]
                rho[product_column] = evaluate(step['before'])*evaluate(step['factor']) % relation.MODULUS
                first = records[pairs[index][0]]
                auxiliary = first['b'][0][0]
                rho[auxiliary] = (evaluate(step['before'])-evaluate(step['factor']))**2 % relation.MODULUS
            failing = []
            for row in records.values():
                a, b = ([(c, int(v, 16)) for c, v in row[key]] for key in ('a', 'b'))
                if evaluate(a)**2 % relation.MODULUS != evaluate(b): failing.append(row['row'])
            self.assertEqual(failing, [] if n < comparator.ORDER else [endpoint])
        self.assertLess(comparator.ORDER+1, 2**252)


if __name__ == '__main__': unittest.main()
