import copy
import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_native_inverse as native
from circuits import transfer_relation as relation


def fixture():
    accepted = dict(handles=[0, 1, 2, 3], derived={
        0: ((1993, 1),), 1: ((1980, 1),), 2: ((1981, 1),), 3: ((1990, 1),)})
    source=dict(role='authorization.ivk',graph=dict(domain=16,arity=3,width=6),inputs=['nk','ak_x','ak_y'])
    selected = dict(calls=[dict(parameters=dict(width=6),call=source,role='authorization.ivk',
                               segments=[dict(index=0,before=[((0,784),),((1993,1),),((1980,1),),((1981,1),),(),()])])],
        observations=dict(nk=('linear',((1993,1),)),ak_x=('linear',((1980,1),)),ak_y=('linear',((1981,1),))))
    metadata = dict(constant_copy=200692)
    plan = dict(checked=dict(metadata=dict(constant_copy=200692)))
    return accepted, selected, metadata, plan


class NativeInverseTests(unittest.TestCase):
    def generate(self, values):
        accepted, selected, metadata, plan = values
        with patch.object(native.hashes, 'select_ivk', return_value=(selected, metadata, [])), \
                patch.object(native.hashes.ivk, 'inspect_metadata', return_value=accepted), \
                patch.object(native.reduction, 'plan', return_value=plan):
            return native.generate(b'ivk', {}, b'reduction', {}, 'params', '0'*64)

    def test_owned_seed_and_defined_native_sdk_guard(self):
        name, source = self.generate(fixture())
        self.assertEqual(name, 'RuntimeTransferIvkNativeInverseOwned')
        self.assertEqual(source.count('#check @'), 1)
        self.assertEqual(source.count('#print axioms'), 1)
        self.assertNotIn('namespace S :=', source)
        self.assertIn('ShielddViewingKeySeed.seeded_hash_legal', source)
        self.assertIn('ShielddViewingKeyAdmission.incomingScalar', source)
        self.assertIn('actual_inputs', source)
        theorem = source.split('theorem original_rows_complete', 1)[1].split(' := by', 1)[0]
        self.assertNotIn('Satisfies base', theorem)
        self.assertNotIn('eval base', theorem)
        self.assertNotIn('codec.decode', theorem)
        self.assertIn('base 200692 = base 0', theorem)

    def test_exact_native_input_singletons_and_order(self):
        for mutation in ('swap', 'coefficient', 'extra'):
            values = copy.deepcopy(fixture())
            inputs = values[0]['derived']
            if mutation == 'swap':
                inputs[0], inputs[1] = inputs[1], inputs[0]
            elif mutation == 'coefficient':
                inputs[0] = ((1993, 2),)
            else:
                inputs[0] = ((1993, 1), (1994, 1))
            with self.subTest(mutation=mutation), self.assertRaises(relation.RelationError):
                self.generate(values)

    def test_width_domain_arity_and_copy_role_refusals(self):
        for mutation in ('width', 'domain', 'arity', 'copy_seed', 'copy_constant', 'copy_join'):
            values = copy.deepcopy(fixture())
            call = values[1]['calls'][0]
            if mutation == 'width':
                call['parameters']['width'] = 3
            elif mutation == 'domain':
                call['call']['graph']['domain'] = 15
            elif mutation == 'arity':
                call['call']['inputs'].append('extra')
            elif mutation == 'copy_seed':
                values[2]['constant_copy'] = values[3]['checked']['metadata']['constant_copy'] = 1993
            elif mutation == 'copy_constant':
                values[2]['constant_copy'] = values[3]['checked']['metadata']['constant_copy'] = 0
            else:
                values[3]['checked']['metadata']['constant_copy'] += 1
            with self.subTest(mutation=mutation), self.assertRaises(relation.RelationError):
                self.generate(values)

    def test_real_nested_observer_domain_and_input_lcs_fail_closed(self):
        for mutation in ('missing_call','bool_domain','tag','order','input_lc','role'):
            values=copy.deepcopy(fixture());selected=values[1];call=selected['calls'][0]
            if mutation=='missing_call':call.pop('call')
            elif mutation=='bool_domain':call['call']['graph']['domain']=True
            elif mutation=='tag':call['segments'][0]['before'][0]=((0,783),)
            elif mutation=='order':call['call']['inputs']=['ak_x','nk','ak_y']
            elif mutation=='input_lc':selected['observations']['nk']=('linear',((1993,2),))
            else:call['call']['role']='authorization.rnk'
            with self.subTest(mutation=mutation),self.assertRaises(relation.RelationError):self.generate(values)


if __name__ == '__main__':
    unittest.main()
