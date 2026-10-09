import copy
import unittest
from unittest.mock import patch

from circuits import generate_transfer_ivk_parameter_readers as readers
from circuits import transfer_relation as relation


def fixture():
    params = dict(width=6, ark=[[0]*6 for _ in range(65)], mds=[[0]*6 for _ in range(6)])
    params['ark'][0][0] = relation.MODULUS-1
    return dict(calls=[dict(parameters=params,call=dict(role='authorization.ivk',graph=dict(domain=16,arity=3,width=6),inputs=['nk','x','y']),
        role='authorization.ivk',segments=[dict(index=0,before=[((0,784),),((1993,1),),((1980,1),),((1981,1),),(),()])])],
        observations=dict(nk=('linear',((1993,1),)),x=('linear',((1980,1),)),y=('linear',((1981,1),))))


class ParameterReaderTests(unittest.TestCase):
    def generate(self, selected):
        with patch.object(readers.hashes, 'select_ivk', return_value=(selected, {}, [])):
            return readers.generate(b'accepted', {}, 'params', '0'*64)

    def test_all426_entries_checked_against_signed_actual_data(self):
        name, source = self.generate(fixture())
        self.assertEqual(name, 'RuntimeTransferIvkParameterReaders')
        self.assertEqual(source.count('#check @'), 2)
        self.assertEqual(source.count('#print axioms'), 2)
        self.assertIn('List.finRange 426', source)
        self.assertIn('signed entry % (Scalar.modulus : Int)', source)
        self.assertIn('Compiler.coefficient_mod', source)
        self.assertIn('ShielddNativeParameterRead.circuit_parse_value', source)
        self.assertIn('ShielddNativeParameterRead.sdk_parse_value', source)
        for theorem in ('circuit_loaded', 'sdk_loaded'):
            statement = source.split('theorem '+theorem, 1)[1].split(' := by', 1)[0]
            self.assertNotIn('Satisfies', statement)
            self.assertNotIn('canonical :', statement)
            self.assertNotIn('same :', statement)

    def test_recipe_scope_refusals(self):
        for key, value in (('domain', 17), ('inputs', ['nk', 'x'])):
            selected = fixture()
            if key=='domain':selected['calls'][0]['call']['graph'][key]=value
            else:selected['calls'][0]['call'][key]=value
            with self.subTest(key=key), self.assertRaises(relation.RelationError):
                self.generate(selected)

    def test_table_shape_and_canonical_coefficients_refused(self):
        for mutation in ('rounds', 'mds', 'width', 'negative', 'overflow', 'bool'):
            selected = copy.deepcopy(fixture())
            params = selected['calls'][0]['parameters']
            if mutation == 'rounds':
                params['ark'].pop()
            elif mutation == 'mds':
                params['mds'][0].pop()
            elif mutation == 'width':
                params['width'] = 3
            else:
                params['ark'][0][0] = {'negative': -1, 'overflow': relation.MODULUS, 'bool': True}[mutation]
            with self.subTest(mutation=mutation), self.assertRaises(relation.RelationError):
                self.generate(selected)


if __name__ == '__main__':
    unittest.main()
