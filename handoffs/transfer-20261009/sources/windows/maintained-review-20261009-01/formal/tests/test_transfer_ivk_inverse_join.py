import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_inverse_join as inverse_join
from circuits import transfer_relation as relation
from tests import test_transfer_ivk_reduction_original as originals


def fixture():
    plan = originals.fixture()
    rows = plan['inverse']['rows']
    denominator = tuple((2000+i, 2**i) for i in range(252))
    inverse = dict(rows=rows, quotient=2252, product=70000, auxiliary=70001,
        numerator=((0, 1),), denominator=denominator, remainder=())
    stage = dict(left=((2252, 1),), right=denominator, remainder=(),
        output=70000, auxiliary=70001)
    copycol = plan['checked']['metadata']['constant_copy']
    outline = lambda terms: tuple((copycol if c == 0 else c, v) for c, v in terms)
    for index, row in zip(rows, inverse_join.joins._stage_rows(stage)):
        plan['raw'][index] = tuple(outline(terms) for terms in row)
    plan['raw'][rows[-1]] = (outline(((0, 1), (70000, -1))), ())
    plan['inverse'] = inverse
    return plan


class InverseJoinTests(unittest.TestCase):
    def generate(self, plan):
        with patch.object(inverse_join.reduction, 'plan', return_value=plan):
            return inverse_join.generate(b'fixture', {}, {}, '0'*64)

    def test_global_hash_legality_and_constructed_prior_rows(self):
        _, source = self.generate(fixture())
        self.assertEqual(source.count('#check @'), 5)
        self.assertIn('Poseidon.hash6', source)
        self.assertNotIn('Poseidon.hash3', source)
        self.assertIn('ScalarWrittenValue.remainder_nonzero', source)
        self.assertIn('GroupRowCompletion.preserves_rows', source)
        statement = source[source.index('theorem original_complete'):]
        statement = statement[:statement.index(' :=')]
        self.assertNotIn('Satisfies base', statement)
        self.assertNotIn('eval base I.denominator', statement)
        self.assertIn('codec.decode (Poseidon.hash6', statement)
        self.assertEqual(source.count('private theorem support'), 48)

    def test_exact_denominator_and_three_write_frame_refusals(self):
        for mutation in ('denominator', 'collision', 'extra'):
            plan = fixture()
            if mutation == 'denominator':
                plan['inverse']['denominator'] = plan['inverse']['denominator'][:-1]
            elif mutation == 'collision':
                plan['inverse']['product'] = plan['phases'][0]['stages'][0]['output']
            else:
                plan['raw'][max(plan['raw'])+1] = ((), ())
            with self.subTest(mutation=mutation), self.assertRaises(relation.RelationError):
                self.generate(plan)

    def test_constructed_inverse_is_total_for_independently_legal_inputs(self):
        plan = fixture()
        order = inverse_join.reduction.reduction.ORDER
        modulus = relation.MODULUS
        for n in (1, order-1, 8*order+1, modulus-1):
            q, r = divmod(n, order)
            self.assertNotEqual(r, 0)
            rho = {0:1, 60000:1, 3:n, 1994:q, 1995:r}
            rho.update({1996+i:(q>>i)&1 for i in range(4)})
            rho.update({2000+i:(r>>i)&1 for i in range(252)})
            value = lambda terms: sum(rho.get(c, 0)*v for c, v in terms) % modulus
            for stages in [*(phase['stages'] for phase in plan['phases']), [plan['gate_stage']]]:
                for stage in stages:
                    left, right, remainder = (value(stage[key]) for key in ('left', 'right', 'remainder'))
                    rho[stage['output']] = (left*right-remainder) % modulus
                    rho[stage['auxiliary']] = (left-right)**2 % modulus
            before = dict(rho)
            rho[2252] = pow(r, -1, modulus)
            rho[70000] = 1
            rho[70001] = (rho[2252]-r)**2 % modulus
            self.assertTrue(all(rho[c] == v for c, v in before.items()))
            for index, (a, b) in plan['raw'].items():
                self.assertEqual(value(a)**2 % modulus, value(b), (n, index))
        # The exact inverse assertion fails for a zero decoded remainder.
        self.assertNotEqual((1-0)**2 % modulus, 0)


if __name__ == '__main__':
    unittest.main()
