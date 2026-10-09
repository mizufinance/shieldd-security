import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_precompute_tables as generator
from circuits.transfer_relation import RelationError


def fixture():
    checked=dict(metadata=dict(schema='shieldd-transfer-ownership-v1',window_start=0,constant_copy=200692),
        derived={(1,i):((i,1),) for i in [1504,1505,2253,2254,2255,2256,2000,2001]},
        bits=[(1,2000),(1,2001)],points={})
    for role,columns in zip(('base','twice','triple'),((1504,1505),(2253,2254),(2255,2256))):
        checked['points'][role]=tuple(('source',(1,i)) for i in columns)
    cones=dict(cones=[dict(role='formula0',inputs=['x','y'])],
        observations=dict(x=('source',((1504,1),)),y=('source',((1505,1),))))
    plan=dict(point_groups=[dict(material_end=0,stage_end=2),dict(material_end=2,stage_end=4)],
        stages=[dict(quotient=i) for i in range(2253,2257)])
    return checked,cones,plan


class PrecomputeTablesTests(unittest.TestCase):
    def render(self,values,readonly=(((1980,1),),((1981,1),),((3766,1),))):
        checked,cones,plan=values
        with patch.object(generator.native,'generate',return_value=('RuntimeOwnershipWindow000NativePrecompute','source')), \
             patch.object(generator.completion.owner,'cone_certificates',return_value=cones), \
             patch.object(generator.completion,'window_plan',return_value=plan):
            return generator.generate(checked,{},readonly)

    def test_constructed_table_rows_and_values_not_output_premises(self):
        name,source=self.render(fixture())
        self.assertEqual(name,'RuntimeOwnershipWindow000NativeTables')
        self.assertEqual(source.count('#check @'),5)
        self.assertEqual(source.count('#print axioms'),5)
        self.assertIn('native_precompute_complete',source)
        self.assertIn('native_inputs',source)
        self.assertIn('ShielddPointCoordinateSeed.seed_preserves',source)
        self.assertIn('sourceColumns : List Nat := [0, 1980, 1981, 2000, 2001, 3766, 200692]',source)
        self.assertIn('GroupFixedCircuitCompletion.point',source)
        self.assertIn('private theorem triple_coordinates',source)
        self.assertIn('private theorem identity_coordinates',source)
        self.assertIn('List.mem_flatten.mp',source)
        self.assertNotIn('have checked : sourceColumns.all',source)
        self.assertNotIn('program,point,eval',source)
        statement=source.split('theorem table_coordinates',1)[1].split(' := by',1)[0]
        premises=statement.split(' :\n',1)[0]
        self.assertNotIn('Satisfies',premises)
        self.assertNotIn('OnCurve',premises)
        self.assertNotIn('tableMeaning',premises)
        self.assertIn('model.coordinates (3 •',statement)

    def test_full_bit_source_certificates_have_bounded_private_checks(self):
        checked,cones,plan=fixture()
        checked['bits']=[(1,column) for column in range(2000,2252)]
        checked['derived'].update({handle:((handle[1],1),) for handle in checked['bits']})
        _,source=self.render((checked,cones,plan))
        self.assertEqual(source.count('private theorem source_checked'),17)
        self.assertEqual(source.count('#check @'),5)
        self.assertEqual(source.count('#print axioms'),5)

    def test_changed_actual_table_seed_alias_or_wrong_family_refuses(self):
        for change in ('twice','triple','base','seed_alias','pair','family','later'):
            values=copy.deepcopy(fixture());checked,cones,plan=values
            if change in ('twice','triple','base'):
                checked['points'][change]=checked['points']['base'] if change!='base' else checked['points']['twice']
            elif change=='seed_alias':checked['bits'][0]=(1,1504)
            elif change=='pair':plan['point_groups'][0]['stage_end']=1
            elif change=='family':checked['metadata']['schema']='shieldd-transfer-rnk-dh-v1'
            else:checked['metadata']['window_start']=16
            with self.subTest(change=change),self.assertRaises(RelationError):self.render(values)


if __name__=='__main__':unittest.main()
