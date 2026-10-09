import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_native_scalar as generator
from circuits.transfer_relation import RelationError


class NativeScalarTests(unittest.TestCase):
    def test_owned_native_scalar_and_coordinate_reader_supply_all_endpoint_inputs(self):
        cones=dict(cones=[dict(role='formula0',inputs=['x','y'])],
            observations=dict(x=('source',((1504,1),)),y=('source',((1505,1),))))
        with patch.object(generator.native,'generate',return_value=('validated','source')), \
             patch.object(generator.scalar_rows,'generate',return_value=('validated','source')), \
             patch.object(generator.native.tables.completion.owner,'cone_certificates',return_value=cones):
            name,source=generator.generate([dict(metadata=dict(constant_copy=200692))],[{}],
                b'ivk',{},b'reduction',{},'params','a'*64)
        self.assertEqual(name,'RuntimeOwnershipNativeScalar')
        self.assertEqual(source.count('#check @'),1)
        self.assertEqual(source.count('#print axioms'),1)
        self.assertIn('RuntimeOwnershipNativeConstructor.native_windows_complete',source)
        self.assertIn('RuntimeOwnershipNativeConstructor.native_bit_values',source)
        self.assertIn('RuntimeOwnershipNativeScalarFrame.completed_base',source)
        self.assertIn('RuntimeOwnershipConstructedScalar.scalar_coordinates',source)
        self.assertIn('lt_trans (fr.bounded scalar)',source)
        premises=source.split('theorem native_scalar_coordinates',1)[1].split(' :\n',1)[0]
        self.assertNotIn('Satisfies',premises)
        self.assertNotIn('baseRole',premises)
        self.assertNotIn('written',premises)
        self.assertNotIn('scalarMeaning',premises)
        self.assertNotIn('endpointRows',source)
        self.assertNotIn('target_role',source)

    def test_requires_actual_ownership_constructor_join(self):
        with patch.object(generator.native,'generate',side_effect=RelationError('native source mismatch')):
            with self.assertRaises(RelationError):generator.generate([],[],b'',{},b'',{},'params','a'*64)

    def test_complete_producer_inventory_includes_ordered_scalar_supports(self):
        chunks=[dict(metadata=dict(constant_copy=200692),bits=[0],derived={0:((2000,1),)})]
        cones=dict(cones=[dict(role='formula0',inputs=['x','y'])],
            observations=dict(x=('source',((1504,1),)),y=('source',((1505,1),))))
        with patch.object(generator,'generate',return_value=('RuntimeOwnershipNativeScalar','native endpoint')) as checked, \
             patch.object(generator.native.tables.completion.owner,'cone_certificates',return_value=cones):
            modules=generator.generate_modules(chunks,[{}],b'ivk',{},b'reduction',{},'params','a'*64)
        checked.assert_called_once()
        self.assertEqual(len(modules),13)
        names=list(modules)
        self.assertEqual(names[0],'RuntimeOwnershipConstructedTraceFacts')
        self.assertEqual(names[1:8],[f'RuntimeOwnershipConstructedTraceTail{offset:03d}' for offset in reversed(range(7))])
        self.assertEqual(names[8:],['RuntimeOwnershipConstructedScalar',
            'RuntimeOwnershipNativeScalarConstants','RuntimeOwnershipNativeScalarBase',
            'RuntimeOwnershipNativeScalarFrame','RuntimeOwnershipNativeScalar'])
        self.assertEqual(sum(source.count('#check @') for source in list(modules.values())[:-1]),31)
        self.assertEqual(modules[names[-1]],'native endpoint')

    def test_native_helpers_derive_same_assignment_without_output_premises(self):
        modules=generator._render_modules(200692,1504,1505)
        combined=generator._render_combined(200692,1504,1505)[1]
        main=modules['RuntimeOwnershipNativeScalar']
        statement=lambda source: source.split('theorem native_scalar_coordinates',1)[1].split(' := by',1)[0]
        self.assertEqual(statement(combined),statement(main))
        self.assertEqual(sum(source.count('#check @') for source in modules.values()),7)
        for source in modules.values():
            self.assertNotIn('(constructed :',source)
            self.assertNotIn('(written :',source)
            self.assertNotIn('(baseRole :',source)
            self.assertNotIn('target_role',source)
            self.assertLess(source.rfind('\nimport '),source.index('set_option maxHeartbeats'))
        self.assertIn('RuntimeOwnershipWindow000NativeTables.table_coordinates',modules['RuntimeOwnershipNativeScalarBase'])
        self.assertIn('column ∈ List.range 2257 ++ [3766,200692]',modules['RuntimeOwnershipNativeScalarFrame'])


if __name__=='__main__':unittest.main()
