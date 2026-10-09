"""Finite source-formula fixtures; no runtime capture or proof credit."""
import copy
import unittest
from circuits import transfer_balance_shared_add as shared
from circuits import transfer_balance_final_add as final, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests.test_transfer_balance_final_add import fixture as affine_fixture


def fixture():
    roles = affine_fixture()[0]
    rows = []
    def emit(a, b):
        outline = lambda lc: canonical((200692 if c == 0 else c, v) for c, v in lc)
        rows.append(dict(row=len(rows), a=[[c, f'{v:064x}'] for c, v in outline(a)],
                         b=[[c, f'{v:064x}'] for c, v in outline(b)]))
    def product(left, right, column, auxiliary=None):
        out, aux = ((column, 1),), ((column+1 if auxiliary is None else auxiliary, 1),)
        emit(combine(left, right, -1), aux)
        emit(combine(left, right), combine(aux, out, 4))
        return out
    sign = product(roles['negative'], ((10, relation.MODULUS-2),), 50)
    signed = combine(roles['unsigned'][0], sign), roles['unsigned'][1]
    xx = product(signed[0], roles['blinded'][0], 52)
    yy = product(signed[1], roles['blinded'][1], 54)
    xy = product(xx, yy, 56)
    dt = canonical((c, final.D*v) for c, v in xy)
    plus, minus = combine(final.ONE, dt), combine(final.ONE, dt, -1)
    denominator = product(plus, minus, 58)
    inverse = ((90, 1),)
    inverse_product = product(inverse, denominator, 60)
    cross_x = product(signed[0], roles['blinded'][1], 62)
    cross_y = product(signed[1], roles['blinded'][0], 64)
    x_minus = product(combine(cross_x, cross_y), minus, 66)
    product(x_minus, inverse, 160, 162)
    y_plus = product(combine(yy, xx), plus, 68)
    product(y_plus, inverse, 161, 163)
    # Compiler assertions follow ALL node products. The inverse equality is
    # not assumed when the matcher discovers its physical witness column.
    emit(combine(inverse_product, final.ONE, -1), ())
    rows.append(dict(row=len(rows), a=[[0, f'{1:064x}'],
                     [200692, f'{relation.MODULUS-1:064x}']], b=[]))
    identity = dict(relation_digest=final.DIGEST, domain_size=262144, stored_rows=200770)
    return roles, rows, identity


class SharedAddTests(unittest.TestCase):
    def test_retained_actual_reciprocal_pair_positive_assignments(self):
        # Diagnostic02 is a real original-row slice, not a qualified local
        # completion. Check its two physical rows independently of the matcher
        # and without fabricating the delayed assertion or a source page.
        import json
        from pathlib import Path
        path = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/balance-final-rows-diagnostic-02/selected.json')
        retained = json.loads(path.read_bytes())
        self.assertTrue(retained['diagnostics_only'])
        self.assertFalse(retained['qualification'])
        self.assertEqual(retained['identity']['relation_digest'], final.DIGEST)
        pair = {row['row']: row for row in retained['selected_rows'] if row['row'] in (172484,172485)}
        self.assertEqual(set(pair), {172484,172485})
        for denominator in (1,2,17,relation.MODULUS-1):
            q = pow(denominator,-1,relation.MODULUS)
            rho = {22736:q,195220:denominator,195222:1,
                   195223:(q-denominator)**2 % relation.MODULUS}
            for row in pair.values():
                a,b = (sum(rho[c]*int(v,16) for c,v in row[k]) % relation.MODULUS for k in ('a','b'))
                self.assertEqual(a*a % relation.MODULUS,b)

    def test_reversed_native_inverse_assertion_retains_exact_rows(self):
        roles, rows, identity = fixture()
        assertion = rows[-2]
        assertion['a'] = [[c, f'{(-int(v,16)) % relation.MODULUS:064x}'] for c, v in assertion['a']]
        matcher = shared.Matcher(roles)
        for row in rows:
            matcher.observe(row)
        plan = matcher.finish(identity)
        self.assertEqual(plan['selected_rows'], rows)
        from circuits.generate_transfer_balance_shared_add_completion import render_plan
        _, body = render_plan(plan)
        self.assertIn('CompilerSignedCompletion.original_rows', body)
        self.assertEqual(body.count('#print axioms '), 13)
        inverse = next(s for s in plan['stages'] if s['kind'] == 'quotient')
        cert = shared.arithmetic.quotient_certificate(final.ONE, inverse['denominator'], plan['inverse'], matcher.normalized)
        self.assertIsNone(shared.arithmetic.completion_certificate(cert, matcher.normalized))
        self.assertEqual(shared.reciprocal_completion(cert, matcher.normalized),
                         {k:v for k,v in inverse.items() if k not in ('kind','role')})
        altered = dict(matcher.normalized)
        altered[cert['rows'][2]] = altered[cert['rows'][2]][0], ((180,1),)
        self.assertIsNone(shared.reciprocal_completion(cert, altered))

    def test_actual_source_formula_rows_construct_without_two_affine_quotients(self):
        roles, rows, identity = fixture()
        matcher = shared.Matcher(roles)
        for row in rows:
            matcher.observe(row)
        plan = matcher.finish(identity)
        self.assertEqual(plan['lowering'], 'point_shared_inverse')
        self.assertEqual([s['role'] for s in plan['stages'] if s['kind'] == 'quotient'], ['inverse'])
        self.assertEqual(plan['selected_rows'], rows)
        for negative, x, y, bx, by in ((0, 3, 4, 5, 6), (1, 3, 4, 5, 6), (0, 0, 1, 0, 1)):
            rho = {0: 1, 200692: 1, 10: x, 11: y, 12: bx, 13: by, 14: negative}
            evaluate = lambda lc: sum(rho[c]*v for c, v in lc) % relation.MODULUS
            for stage in plan['stages']:
                if stage['kind'] == 'product':
                    left, right = evaluate(stage['left']), evaluate(stage['right'])
                    rho[stage['output']] = (left*right-evaluate(stage['remainder'])) % relation.MODULUS
                    rho[stage['auxiliary']] = (left-right)**2 % relation.MODULUS
                else:
                    numerator, denominator = evaluate(stage['numerator']), evaluate(stage['denominator'])
                    self.assertNotEqual(denominator, 0)
                    rho[stage['quotient']] = numerator*pow(denominator, -1, relation.MODULUS) % relation.MODULUS
                    rho[stage['product']] = (numerator-evaluate(stage['remainder'])) % relation.MODULUS
                    rho[stage['auxiliary']] = (rho[stage['quotient']]-denominator)**2 % relation.MODULUS
            for row in rows:
                a, b = (tuple((c, int(v, 16)) for c, v in row[k]) for k in ('a', 'b'))
                self.assertEqual(evaluate(a)**2 % relation.MODULUS, evaluate(b))
            sx = -x if negative else x
            delta = final.D*sx*bx*y*by % relation.MODULUS
            self.assertEqual(rho[160], (sx*by+y*bx)*pow((1+delta) % relation.MODULUS, -1, relation.MODULUS) % relation.MODULUS)
            self.assertEqual(rho[161], (y*by+sx*bx)*pow((1-delta) % relation.MODULUS, -1, relation.MODULUS) % relation.MODULUS)

    def test_affine_window_formula_and_missing_inverse_assertion_refuse(self):
        for roles, rows, identity in (affine_fixture(), fixture()):
            if len(rows) > 20:
                rows = rows[:-2] + rows[-1:]
            matcher = shared.Matcher(roles)
            for row in rows:
                matcher.observe(row)
            with self.assertRaises(relation.RelationError):
                matcher.finish(identity)

    def test_wrong_output_binding_and_shared_write_refuse(self):
        roles, rows, identity = fixture()
        for variant in ('output', 'readonly'):
            altered = copy.deepcopy(roles)
            if variant == 'output':
                altered['output'] = (((170, 1),), ((171, 1),))
            matcher = shared.Matcher(altered)
            for row in rows:
                matcher.observe(row)
            with self.assertRaises(relation.RelationError):
                matcher.finish(identity, (((50, 1),),) if variant == 'readonly' else ())

    def test_renderer_covers_shared_inverse_rows_and_preserves_legacy_affine_bytes(self):
        from circuits import generate_transfer_balance_final_add_completion as renderer
        from pathlib import Path
        import importlib.util
        roles, rows, identity = fixture()
        matcher = shared.Matcher(roles)
        for row in rows:
            matcher.observe(row)
        plan = matcher.finish(identity)
        name, body = renderer.render_plan(plan)
        self.assertEqual(name, 'RuntimeTransferBalanceFinalAddCompletion')
        self.assertIn('def inverseStep', body)
        self.assertNotIn('GroupQuotientPairCompletion', body)
        self.assertIn('TransferSubgroup.shared_inverse_affine', body)
        self.assertIn('CompilerSignedCompletion.original_rows', body)
        self.assertEqual(body.count('#print axioms '), 13)
        self.assertEqual(body.count('#check @'), 13)
        altered = copy.deepcopy(plan)
        altered['inverse'] = ((91, 1),)
        with self.assertRaises(relation.RelationError):
            renderer.render_plan(altered)
        # A real immutable source09 renderer is the legacy default byte oracle;
        # the new dispatcher cannot silently change those existing outputs.
        path = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/balance-joint-consumer-source-09/source/circuits/generate_transfer_balance_final_add_completion.py')
        module_spec = importlib.util.spec_from_file_location('circuits._retained_final_renderer', path)
        retained = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(retained)
        roles, rows, identity = affine_fixture()
        legacy = final.Matcher(roles)
        for row in rows:
            legacy.observe(row)
        old_plan = legacy.finish(identity)
        self.assertEqual(renderer.render_plan(old_plan), retained.render_plan(old_plan))
