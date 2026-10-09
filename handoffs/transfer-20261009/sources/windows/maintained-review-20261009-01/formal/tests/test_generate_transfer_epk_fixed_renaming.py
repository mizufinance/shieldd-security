"""Bounded source/dispatch tests; no accepted EPK capture is fabricated."""
import io,re,unittest,hashlib
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_renaming as render
from circuits import transfer_epk_fixed_renaming as matcher,transfer_relation as relation
from circuits import transfer_fixed_spend as fixed,generate_transfer_fixed_spend as legacy
from circuits.generate_hash_round import linear
from tests.fixed_spend_fixture import full_fixture


class EpkRenamingRendererTests(unittest.TestCase):
    def test_lookup_certificate_is_bounded_and_derives_injection(self):
        pairs=[(100+i,1000+i) for i in range(140)]
        inverse=sorted(pairs+[(b,a) for a,b in pairs])
        _,source=render._map_source(dict(scope_id=1,permutation=inverse))
        self.assertEqual(source.count('theorem inverse_part'),3)
        self.assertIn('FiniteColumnRenaming.involutive tree inverse_checked',source)
        self.assertIn('FiniteColumnRenaming.injective tree inverse_checked',source)
        self.assertIn('protectedOriginals : List Nat := [0,1,2,6,200692]',source)
        self.assertIn('change ((FiniteColumnRenaming.checkInverse tree part0) &&',source)
        self.assertEqual(source.count('#print axioms'),source.count('set_option pp.all true in'))
        with self.assertRaisesRegex(relation.RelationError,'inverse'):
            render._map_source(dict(scope_id=1,permutation=[(100,1000)]))
        with self.assertRaisesRegex(relation.RelationError,'unique'):
            render._map_source(dict(scope_id=1,permutation=[(100,1000),(100,1000)]))

    def test_row_certificate_retains_exact_actual_coefficients_and_duplicate_order(self):
        pair=dict(original_row_map=[(7,27),(8,28)],restricted_map=[(0,0),(100,500),(101,501)])
        original={7:(((0,1),(100,3)),((101,4),)),8:(((101,1),),())}
        target={27:(((0,1),(500,3)),((501,4),)),28:(((501,1),),())}
        block=dict(module='AuthoredBoundedFixture',definition='rawRows',indices=[7,8,7])
        _,source=render._row_source(1,0,block,pair,original,target)
        self.assertIn('originalRows : List Nat := [27, 28, 27]',source)
        self.assertIn('AuthoredBoundedFixture.rawRows.map',source)
        expected='⟨'+linear(target[27][0])+','+linear(target[27][1])+'⟩'
        self.assertEqual(source.count(expected),2)
        bad=dict(target);bad[27]=(target[27][0],((501,5),))
        with self.assertRaisesRegex(relation.RelationError,'row/LC'):
            render._row_source(1,0,block,pair,original,bad)

    def test_window_order_matches_existing_authored_renderer_including_copy_repeats(self):
        # This is the old synthetic arithmetic fixture, never a runtime EPK
        # schema or a qualification flag. Compare actual renderer output bytes.
        captures,roles,ordinary=full_fixture(ordered_canonical=True,ordered_fixed=True)
        extracted=fixed.extract_rows(captures[0],roles,io.BytesIO(ordinary),include_canonical=False)
        checked,raw,normal,products,quotients,_=fixed._selection(captures[0],roles,extracted)
        for offset in (0,1,15):
            source=legacy.render_window(checked,raw,normal,products,quotients,offset,stem='AuthoredFixture')
            indices=render._window_indices(checked,extracted,offset)
            local_text=re.search(r'def localRows : List Row := \[\n(.*?)\]\ndef rawRows',source,re.S).group(1)
            quotient_text=re.search(r'def rawRows : List Row := \[(.*?)\]\n',source,re.S).group(1)
            authored_rows=''.join((local_text+','+quotient_text).split())
            selected_rows=''.join(','.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in indices).split())
            self.assertEqual(authored_rows,selected_rows)
            self.assertLess(len(set(indices)),len(indices))

    def test_transport_calls_constructor_and_universal_frame_not_desired_truth(self):
        source=dict(scalar=dict(value=17),boundary=dict(published=(((100,1),),((101,1),)),
            inverse_constructor=dict(quotient=102,product=103,auxiliary=104)),
            checked=dict(parent=dict(constant_copy=200692)),
            chunks=[dict(metadata=dict(window_start=i,window_count=min(16,126-i))) for i in range(0,126,16)])
        pair=dict(scope_id=1,restricted_map=[(17,500),(100,510),(101,511),(102,512)])
        _,text=render._transport_source(source,pair,[{}]*129,[0,1,2,6,17,500,200692],[510,511,512])
        self.assertIn('RuntimeTransferEpk0NativeBoundary.cone_rows_complete (pullback base)',text)
        self.assertIn('RowCompletionRenaming.complete_rows',text)
        self.assertIn('RuntimeTransferEpk0NativeBoundary.outside_total',text)
        self.assertIn('theorem native_published',text)
        self.assertIn('theorem inverse_column',text)
        self.assertIn('GroupRowCompletion.quotient_value',text)
        self.assertNotIn('(completed :',text)
        self.assertNotIn('(satisfied :',text)
        self.assertNotIn('(pointNonzero :',text)
        self.assertNotIn('(outputRole :',text)
        self.assertNotIn('VALUE_BLINDING',text)
        self.assertNotRegex(text,r'namespace \w+ :=|\b(?:have|let|intro) (?:local|protected)\b')
        self.assertIn('theorem exact_writes',text)
        self.assertIn('theorem outside_rows',text)
        self.assertEqual(text.count('#print axioms'),21)
        self.assertEqual(text.count('#print axioms'),text.count('set_option pp.all true in'))

    def test_owned_write_order_covers_seed_canonical_loop_and_inverse_once(self):
        # Tiny constructor-role fixture only, not a runtime parent or page.
        source=dict(boundary=dict(published=(((100,1),),((101,1),)),
            inverse_constructor=dict(quotient=900,product=901,auxiliary=902)),
            scalar=dict(bit_start=200,stages=[dict(output=500,auxiliary=501)]),
            loop=dict(programs=[dict(stages=[dict(kind='product',output=600,auxiliary=601),
                dict(kind='linear',output=602),dict(kind='quotient',quotient=700,product=701,auxiliary=702)])]))
        order=[100,101]+list(range(200,452))+[500,501,600,601,602,700,701,702,900,901,902]
        pair=dict(source_writes=sorted(order),target_writes=sorted(c+1000 for c in order),
            restricted_map=[(c,c+1000) for c in order])
        self.assertEqual(render._owned_order(source,pair),[c+1000 for c in order])
        bad=dict(pair,target_writes=pair['target_writes'][:-1])
        with self.assertRaisesRegex(relation.RelationError,'target owned'):
            render._owned_order(source,bad)
        source['loop']['programs'][0]['stages'].append(dict(kind='linear',output=600))
        with self.assertRaisesRegex(relation.RelationError,'constructor write'):
            render._owned_order(source,pair)

    def test_sequence_adapter_uses_exact_transport_and_full_outside_frame(self):
        # Interface/source fixture only; no actual parent, page or qualification.
        source=dict(scalar=dict(value=17),checked=dict(parent=dict(constant_copy=200692)))
        pair=dict(scope_id=3,restricted_map=[(17,500)])
        modules=render._sequence_adapters(source,pair)
        self.assertEqual(set(modules),{'RuntimeTransferEpk3Fixed','RuntimeTransferEpk3NativeBoundary'})
        fixed=modules['RuntimeTransferEpk3Fixed'];boundary=modules['RuntimeTransferEpk3NativeBoundary']
        self.assertIn('rawRows : List Row := ShielddSecurity.RuntimeTransferEpk3RenamedCompletion.fixedRows',fixed)
        self.assertIn('RenamingRows127.rawRows',boundary)
        self.assertIn('RenamingRows128.rawRows',boundary)
        self.assertIn('theorem rows_exact',boundary)
        self.assertIn('RenamedCompletion.outside_column base model generator n column outside',boundary)
        self.assertIn('RenamedCompletion.outside_eval base model generator n terms outside',boundary)
        self.assertIn('RenamedCompletion.original_rows_complete',boundary)
        self.assertIn('(meaning : base 500 = (n : F))',boundary)
        self.assertNotIn('VALUE_BLINDING',boundary)
        self.assertNotRegex(boundary,r'\((?:completed|satisfied|outputRole|pointNonzero) :')
        self.assertEqual(fixed.count('#print axioms'),1)
        self.assertEqual(boundary.count('#print axioms'),4)
        for text in modules.values():
            self.assertEqual(text.count('#print axioms'),text.count('set_option pp.all true in'))

    def test_sequence_dispatch_is_opt_in_and_preserves_full_fallback(self):
        with self.assertRaisesRegex(relation.RelationError,'Boolean'):
            render.generate(b'',[],{},{},{},include_sequence=1)
        accepted=dict(protected=[0,1,2,200692]+list(range(3,9)),
            locals=[dict(scalar=dict(value=3+i)) for i in range(6)],
            steps=[dict(fence=dict(origin=1000,copy=200692,low=300+300*i,
                high=1004+600*i,exceptions=[17+i])) for i in range(6)])
        with patch.object(render.sequence,'plan',return_value=accepted):
            with patch.object(render.matcher,'_pair',side_effect=relation.RelationError('unsupported')):
                with patch.object(render.program,'generate_scope',side_effect=lambda *a,**k:{str(a[5]):'authored source'}):
                    with patch.object(render.sequence,'_render',wraps=render.sequence._render) as compose:
                        default=render.generate(b'',[],{},{},{})
                        compose.assert_not_called()
                        included=render.generate(b'',[],{},{},{},include_sequence=True)
                        compose.assert_called_once_with(accepted)
                        self.assertEqual({k:v for k,v in included['modules'].items() if k!='RuntimeTransferEpkSixCompletion'},default['modules'])
                        self.assertIn('theorem six_cones_complete',included['modules']['RuntimeTransferEpkSixCompletion'])
                        self.assertEqual(included['modules']['RuntimeTransferEpkSixCompletion'].count('#print axioms'),34)
                        self.assertFalse(included['qualification'])

    def test_default_transport_bytes_match_frozen_pre_sequence_renderer(self):
        # These authored-fixture output hashes were compared byte-for-byte with
        # the immutable source03 predecessor before this interface was added.
        # They assert regression identity, never accepted runtime metadata.
        digest=lambda result:hashlib.sha256(result[1].encode()).hexdigest()
        source=dict(scalar=dict(value=17),boundary=dict(published=(((100,1),),((101,1),)),
            inverse_constructor=dict(quotient=102,product=103,auxiliary=104)),
            checked=dict(parent=dict(constant_copy=200692)),
            chunks=[dict(metadata=dict(window_start=i,window_count=min(16,126-i))) for i in range(0,126,16)])
        pair=dict(scope_id=1,restricted_map=[(17,500),(100,510),(101,511),(102,512)])
        arguments=(source,pair,[{}]*129,[0,1,2,6,17,500,200692],[510,511,512])
        self.assertEqual(digest(render._transport_source(*arguments)),
                         '2bba93585b4d497dbda387295c57593bb5212557f75129e4f7769db3b98ed51b')
        mapping=dict(scope_id=1,permutation=[(100,1000),(1000,100)])
        self.assertEqual(digest(render._map_source(mapping)),
                         'e9abb21126aebc27a74bfd9e94ef87f673770cd879cc1b031d120d64d7fe84c8')
        rows_pair=dict(original_row_map=[(7,27)],restricted_map=[(0,0),(100,500)])
        block=dict(module='AuthoredFixture',definition='rawRows',indices=[7,7])
        original={7:(((0,1),(100,3)),())};target={27:(((0,1),(500,3)),())}
        self.assertEqual(digest(render._row_source(1,0,block,rows_pair,original,target)),
                         '6c20a938313616711227037695ef80206a21f4ac838871288f2dd8d4d277aa9a')

    def test_unqualified_refusal_precedes_fallback_and_fallback_remains_full(self):
        with patch.object(render.sequence,'plan',side_effect=relation.RelationError('unqualified')):
            with patch.object(render.program,'generate_scope') as fallback:
                with self.assertRaisesRegex(relation.RelationError,'unqualified'):
                    render.generate(b'',[],{},{},{})
                fallback.assert_not_called()
        # Dispatch test only: no fixture is published as accepted runtime data.
        with patch.object(render.sequence,'plan',return_value={'dispatch_fixture':True}):
            with patch.object(render.matcher,'_pair',side_effect=relation.RelationError('unsupported shape')):
                with patch.object(render.program,'generate_scope',side_effect=lambda *a,**k:{str(a[5]):'authored source'}) as fallback:
                    result=render.generate(b'',[],{},{},{})
                    self.assertEqual(result['mode'],'full-per-scope')
                    self.assertEqual(set(result['modules']),set(map(str,range(6))))
                    self.assertEqual(fallback.call_count,6)
                    self.assertTrue(all(call.kwargs=={'include_local':True} for call in fallback.call_args_list))
                    self.assertFalse(result['qualification'])
                    with self.assertRaisesRegex(relation.RelationError,'unsupported'):
                        render.generate(b'',[],{},{},{},require_renaming=True)


if __name__=='__main__':unittest.main()
