import copy,unittest
from circuits import transfer_balance_input_layout as layout,transfer_relation as relation

class BalanceInputLayoutTests(unittest.TestCase):
    def fixture(self):
        return dict(identity=dict(source_blocks=[[[1,6]]],source_public=[[1,22734]],stored_rows=200770,domain_size=262144),
            templates=[dict(row=layout.ROW,roles=['layout.committed-shadow'])],
            selected_rows=[dict(row=layout.ROW,a=[[c,format(v,'x')] for c,v in layout.EXPECTED[0]],b=[])])
    def test_native_source_shadow_is_distinct_from_committed_target_and_row_mandatory(self):
        self.assertEqual(layout.source_role({'source':[1,6]},((9,1),)),dict(source=[1,6],target=2,shadow=9))
        selected=layout.selected(self.fixture());name,source=layout.render(selected)
        self.assertEqual(name,'RuntimeBalanceInputLayout')
        self.assertIn('CompilerLinearCompletion.extend base [(2,1)] [] 9',source)
        self.assertIn('theorem binding',source)
        self.assertNotIn('(linked :',source)
        self.assertEqual(source.count('#print axioms '),6)
        self.assertEqual(source.count('#check @'),6)
    def test_refuses_source_alias_changed_position_polynomial_and_layout(self):
        with self.assertRaises(relation.RelationError):layout.source_role({'source':[1,6]},((2,1),))
        for edit in ['position','polynomial','layout']:
            with self.subTest(edit=edit):
                data=self.fixture()
                if edit=='position':data['templates'][0]['row']-=1
                elif edit=='polynomial':data['selected_rows'][0]['a'][0][1]='2'
                else:data['identity']['source_blocks']=[[[1,7]]]
                with self.assertRaises(relation.RelationError):layout.selected(data)

    def test_public_source_descriptor_protects_shadow_not_h_output(self):
        identity=self.fixture()['identity']
        identity['relation_digest']='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'
        self.assertEqual(layout.public_witness_shadows(identity),(22737,))
        self.assertNotIn(22734,layout.public_witness_shadows(identity))
        for field,value in [('source_public',[[0,22734]]),('source_blocks',[[[1,7]]]),
                            ('stored_rows',200769),('relation_digest','0'*64)]:
            altered=copy.deepcopy(identity);altered[field]=value
            with self.subTest(field=field),self.assertRaises(relation.RelationError):
                layout.public_witness_shadows(altered)

    def test_signed_identity_extension_requires_all_old_fields_and_real_header(self):
        current=self.fixture()['identity']
        current.update(schema='shieldd-transfer-relation-v1',raw_sha256='a'*64,scope='identity only',
            relation_digest='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236')
        previous={key:value for key,value in current.items() if key not in ('source_public','source_blocks')}
        self.assertTrue(layout.same_original_identity(previous,current))
        self.assertTrue(layout.same_original_identity(current,current))
        for field,value in [('raw_sha256','b'*64),('stored_rows',200769),('scope','other')]:
            bad=copy.deepcopy(previous);bad[field]=value
            self.assertFalse(layout.same_original_identity(bad,current))
        bad=copy.deepcopy(current);bad['source_public']=[[1,22731]]
        self.assertFalse(layout.same_original_identity(previous,bad))
        bad=copy.deepcopy(previous);bad['unexpected']=1
        self.assertFalse(layout.same_original_identity(bad,current))
