"""Local zero/nonzero construction from arbitrary actual auxiliary values."""
import io
import copy
import json
import re
import unittest
from blake3 import blake3

from circuits import transfer_asset_map as maps, transfer_relation as relation
from circuits import transfer_asset_map_total_inverse_completion as inverse
from tests.test_transfer_asset_map import fixture, encoded
from tests.test_asset_asserted_squares import defer_captured
from circuits.transfer_balance_rows import canonical, combine


def fused_inverse_fixture():
    """Toy original-row fused targets; never asserted to be a runtime capture."""
    data, caller, stream, _, builder = fixture(17)
    checked = maps.inspect_metadata(data, caller);obj = json.loads(data)
    records = [json.loads(line) for line in stream.getvalue().splitlines()]
    copy_column = obj['constant_copy']
    outline = lambda lc: canonical((copy_column if c == 0 else c, n) for c, n in lc)
    rows = [(canonical((c, int(n, 16)) for c, n in row['a']),
             canonical((c, int(n, 16)) for c, n in row['b'])) for row in records[1:-1]]
    targets = (combine(maps.ONE, checked['values']['zero'], -1), (), ())
    for ref, old, target in zip(obj['constraint_products'][1:], checked['products'][1:], targets):
        for offset, (a, b) in enumerate(rows):
            if b and any(c in dict(old) for c, _ in b):
                rows[offset] = (a, combine(b, outline(combine(target, old, -1)), 4))
        rows.remove((outline(combine(old, target, -1)), ()))
        expression = next(e for e in obj['expressions'] if e['source'] == ref['source'])
        expression['terms'] = [[c, f'{n:064x}'] for c, n in target]
    header = records[0];domain = obj['domain_size'];digest = blake3()
    digest.update(relation.NAMESPACE + relation.u64(domain) + relation.u64(len(rows)) +
                  relation.indices(header['source_public']) + relation.u64(1) +
                  relation.indices(header['source_blocks'][0]))
    records = [dict(row=i, a=[[c, f'{n:064x}'] for c, n in a], b=[[c, f'{n:064x}'] for c, n in b])
               for i, (a, b) in enumerate(rows)]
    for row in records:
        digest.update(b'A' + relation.terms(row['a'], domain) + b'B' + relation.terms(row['b'], domain))
    obj.update(relation_digest=digest.hexdigest(), full_rows=len(rows))
    caller = copy.deepcopy(caller);caller['metadata'].update(relation_digest=digest.hexdigest(), full_rows=len(rows))
    header.update(relation_digest=digest.hexdigest(), stored_rows=len(rows))
    raw = b''.join(encoded(v) for v in [header, *records, dict(eof=True, rows=len(rows))])
    return encoded(obj), caller, raw, builder


class TotalInverseConstructionTests(unittest.TestCase):
    def test_generated_native_branch_has_no_desired_inverse_or_row_premise(self):
        data, caller, stream, _, builder = fixture(17)
        for data, caller, raw, builder in (
                (data, caller, stream.getvalue(), builder),
                fused_inverse_fixture()):
            extracted = maps.extract(data, io.BytesIO(raw), caller)
            name, source = inverse.generate(data, extracted, caller)
            self.assertEqual(name, 'RuntimeTransferAssetMapTotalInverseCompletion')
            exports = re.findall(r'#check @([A-Za-z0-9_]+)', source)
            self.assertEqual(exports, re.findall(r'#print axioms ([A-Za-z0-9_]+)', source))
            self.assertEqual(len(exports), 12)
            self.assertNotRegex(source, r'\b(sorry|admit|axiom|native_decide)\b')
            complete = source[source.index('theorem complete ['):source.index('#print axioms')]
            premises = complete[:complete.index(':= by')]
            self.assertNotIn('(satisfied', premises)
            self.assertNotIn('(legal', premises)
            self.assertNotIn('(nonzero', premises)
            self.assertIn('Elligator.inverse_constraints_complete', source)
            self.assertIn('CompilerSignedCompletion.original_rows', source)
            self.assertIn('column ∉ ownedWrites', source)
            self.assertIn('set_option maxHeartbeats 400000', source)
            self.assertIn('List.mem_singleton,List.not_mem_nil,or_false] at member', complete)

    def test_every_original_inverse_row_and_shared_columns(self):
        data, caller, stream, _, builder = fixture(17)
        for data, caller, raw, builder in (
                (data, caller, stream.getvalue(), builder),
                defer_captured(data, caller, stream.getvalue(), builder),
                fused_inverse_fixture()):
            extracted = maps.extract(data, io.BytesIO(raw), caller)
            recipe = inverse.plan(data, extracted, caller)
            for denominator in (0, 1, 19):
                base = dict(builder.rho)
                base.update({c: 31*c + 17 for c in recipe['owned_writes']})
                base.update({1: 83, 2: 97, 32767: 113})
                # Set the independently built denominator LC, rather than
                # supplying an inverse, zero flag or desired product value.
                c, coefficient = recipe['denominator'][0]
                other = sum(base.get(k, 0)*n for k, n in recipe['denominator'][1:])
                base[c] = (denominator - other) * pow(coefficient, -1, relation.MODULUS) % relation.MODULUS
                built = inverse.construct(data, extracted, caller, base)
                rho = built['assignment']
                self.assertEqual(rho[recipe['zero']], int(denominator == 0))
                self.assertEqual(rho[recipe['inverse']], pow(denominator, -1, maps.P) if denominator else 0)
                self.assertFalse(built['proof'])
                self.assertTrue(all(rho[c] == value for c, value in base.items()
                                    if c not in recipe['owned_writes']))
                evaluate = lambda lc: sum(rho.get(c, 0)*n for c, n in lc) % maps.P
                self.assertTrue(all(evaluate(a)**2 % maps.P == evaluate(b) for a, b in recipe['raw'].values()))
                self.assertEqual([rho[c] for c in (0, 1, 2, 32000, 32767)], [1, 83, 97, 1, 113])
            if not any(pair['assertion'] is not None for pair in recipe['pairs']):
                self.assertTrue(all(pair['pivot'] is None for pair in recipe['pairs']))
                self.assertEqual(len(recipe['owned_writes']), 5)


if __name__ == '__main__':
    unittest.main()
