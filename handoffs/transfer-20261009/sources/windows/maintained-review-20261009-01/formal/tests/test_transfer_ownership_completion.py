import unittest
from unittest.mock import patch

from circuits import transfer_ownership_completion as completion
from circuits import generate_transfer_ownership_completion as generator
from circuits.transfer_balance_rows import canonical, combine
from circuits.transfer_relation import RelationError, MODULUS


def row(index, a, b):
    encode = lambda terms: [[c, format(v % MODULUS, '064x')] for c, v in canonical(terms)]
    return dict(row=index, a=encode(a), b=encode(b))


class OwnershipCompletionTests(unittest.TestCase):
    def fixture(self):
        x, y, square, product, auxiliary = [((c, 1),) for c in (1, 2, 10, 20, 21)]
        rows = [row(1, x, square), row(2, combine(square, y, -1), auxiliary),
                row(3, combine(square, y), combine(auxiliary, product, 4)),
                row(4, x, x), row(99, [(0, 1), (200, -1)], [])]
        observations = {name: ('linear', value) for name, value in
                        (('x', x), ('y', y), ('square', square), ('product', product))}
        cones = []
        for i in range(8, 22):
            identity = 'constant'+str(i);observations[identity] = ('linear', ((0, 1),))
            cones.append(dict(role='formula'+str(i), ordered=[identity], inputs=[],
                              source={identity: dict(kind='constant', value=1)},
                              certificates={identity: dict(kind='constant')}))
        cones[0].update(ordered=['x', 'square'], inputs=['x'],
                        source={'square': dict(kind='mul', left='x', right='x')},
                        certificates={'x': dict(kind='input'),
                                      'square': dict(kind='square', rows=[1])})
        cones[1].update(ordered=['square', 'y', 'product'], inputs=['square', 'y'],
                        source={'product': dict(kind='mul', left='square', right='y')},
                        certificates={'square': dict(kind='input'), 'y': dict(kind='input'),
                                      'product': dict(kind='product', rows=[2, 3], auxiliary=auxiliary)})
        selected = {r['row']: tuple(tuple((c, int(v, 16)) for c, v in r[key]) for key in ('a', 'b'))
                    for r in rows if r['row'] != 4}
        cone_packet = dict(cones=cones, observations=observations, rows=selected)
        quotient_packet = dict(rows={99: selected[99]}, certificates=[
            dict(role=f'quotient.{i}.{axis}', kind='folded', numerator=((0, 1),),
                 denominator=((0, 1),), quotient=((0, 1),), rows=[])
            for i in range(2, 5) for axis in range(2)])
        checked = dict(metadata=dict(constant_copy=200, full_rows=256, domain_size=256,
                                     window_start=0, window_count=1),
                       points=dict(base=[('source', (1, 1)), ('source', (1, 2))],
                                   twice=[('native', 0), ('native', 1)],
                                   triple=[('native', 0), ('native', 1)]),
                       windows=[[[('native', 0), ('native', 1)]]],
                       bits=[(1, 3)], derived={(1, 1): x, (1, 2): y, (1, 3): ((3, 1),)})
        return checked, dict(selected_rows=rows), cone_packet, quotient_packet

    def run_plan(self, fixture, readonly=()):
        checked, extracted, cones, quotients = fixture
        with patch.object(completion.owner, 'cone_certificates', return_value=cones), \
                patch.object(completion.owner, 'quotient_certificates', return_value=quotients):
            return completion.window_plan(checked, extracted, include_precompute=False, readonly_lcs=readonly)

    def test_exact_square_product_and_folded_quotient_sequence(self):
        result = self.run_plan(self.fixture())
        self.assertEqual([stage['kind'] for stage in result['stages']], ['square', 'product'])
        self.assertEqual(result['writes'], [10, 20, 21])
        self.assertEqual(result['local_rows'], [1, 2, 3, 99])
        self.assertEqual(result['outside_scope_rows'], [4])
        self.assertEqual(len(result['folded']), 6)

    def test_addition_reads_constructed_selector_and_retains_both_row_pairs(self):
        fixture = self.fixture();cones=fixture[2]['cones']
        square,product=cones[0],cones[1]
        for position in (0,1):
            identity='constant'+str(8+position)
            cones[position]=dict(role='formula'+str(8+position),ordered=[identity],inputs=[],
                source={identity:dict(kind='constant',value=1)},
                certificates={identity:dict(kind='constant')})
        square['role']='formula20';product['role']='formula16'
        cones[12]=square;cones[8]=product
        plan=self.run_plan(fixture)
        values={0:1,200:1,1:3,2:4,10:77,20:33,21:44}
        evaluate=lambda terms:sum(coefficient*values[column] for column,coefficient in terms)%MODULUS
        for stage in plan['stages']:
            if stage['kind']=='square':values[stage['output']]=(evaluate(stage['input'])**2-evaluate(stage['remainder']))%MODULUS
            elif stage['kind']=='product':
                left,right=evaluate(stage['left']),evaluate(stage['right'])
                values[stage['output']]=(left*right-evaluate(stage['remainder']))%MODULUS
                values[stage['auxiliary']]=(left-right)**2%MODULUS
        self.assertEqual(values[10],9)
        self.assertEqual(values[20],36)
        for actual in fixture[1]['selected_rows']:
            if actual['row'] not in plan['local_rows']:continue
            a,b=[tuple((column,int(value,16)) for column,value in actual[key]) for key in ('a','b')]
            self.assertEqual(evaluate(a)**2%MODULUS,evaluate(b))

    def test_protected_pivot_refusal(self):
        with self.assertRaisesRegex(RelationError, 'write aliases'):
            self.run_plan(self.fixture(), [((10, 1),)])

    def test_duplicate_physical_square_refusal(self):
        fixture = self.fixture();fixture[1]['selected_rows'].insert(1, row(5, [(1, 1)], [(10, 1)]))
        fixture[1]['selected_rows'].sort(key=lambda value: value['row'])
        with self.assertRaisesRegex(RelationError, 'unique square physical row'):
            self.run_plan(fixture)

    def test_missing_local_coverage_refusal(self):
        fixture = self.fixture();fixture[2]['rows'][4] = (((1, 1),), ((1, 1),))
        with self.assertRaisesRegex(RelationError, 'every local materialization'):
            self.run_plan(fixture)

    def test_malformed_readonly_fail_closed(self):
        for readonly in ([[(1,)]], [[(1, True)]], 'bad'):
            with self.subTest(readonly=readonly), self.assertRaises(RelationError):
                self.run_plan(self.fixture(), readonly)

    def test_renderer_keeps_local_legality_and_scope_explicit(self):
        fixture = self.fixture();checked, extracted, cones, quotients = fixture
        with patch.object(completion.owner, 'cone_certificates', return_value=cones), \
                patch.object(completion.owner, 'quotient_certificates', return_value=quotients):
            name, source = generator.generate(checked, extracted, include_precompute=False)
        self.assertEqual(name, 'RuntimeOwnershipWindow000Completion')
        self.assertEqual(source.count('#check @'), 4)
        self.assertEqual(source.count('#print axioms'), 4)
        self.assertIn('.compiler (.square', source)
        self.assertIn('.compiler (.product', source)
        self.assertIn('GroupCircuitOrder.checked_order', source)
        self.assertIn('CompilerCompletion.squareRows', source)
        statement = source.split('theorem local_rows_complete', 1)[1].split(' :=', 1)[0]
        self.assertIn('GroupCircuitCompletion.Legal base completionSteps', statement)
        self.assertNotIn('Satisfies base', statement)
        self.assertNotIn('target', statement)


if __name__ == '__main__':
    unittest.main()
