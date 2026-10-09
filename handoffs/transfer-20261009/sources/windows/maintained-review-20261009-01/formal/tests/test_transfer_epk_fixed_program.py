"""Exact plan/legacy-byte source tests only; actual EPK capture UNRUN."""
import importlib.util,io,unittest
from pathlib import Path
from circuits import transfer_fixed_spend as fixed,generate_transfer_fixed_spend as render
from circuits import transfer_epk_fixed_composition as composition,transfer_epk_fixed_program as program
from circuits import transfer_relation as relation
from tests.fixed_spend_fixture import full_fixture


class EpkProgramTests(unittest.TestCase):
    def test_private_cross_page_accumulator_is_not_a_caller_role(self):
        # Two physically owned previous output columns appear as local inputs
        # on the next page. Earlier original rows still remain in freshness.
        self.assertEqual(composition._loop_kept({0,1,2,200692,2000,2001,17},
            {2000,2001,2002,2003},{0,1,2,200692,17}),[0,1,2,17,200692])
        with self.assertRaisesRegex(relation.RelationError,'caller/shared'):
            composition._loop_kept({0,1,17,2000},{2000,2001},{0,1,17,2000})

    def test_whole_ingress_refuses_unqualified_or_mismatched_union_before_generation(self):
        for extracted in ({},dict(fixed={},canonical={},boundaries={},parent_sha256='a'*64,
                raw_page_sha256=[],ordinary_replays=True,scope='fixture')):
            with self.assertRaises(relation.RelationError):program.plan(b'',[],{}, {},extracted,0)

    def test_frame_and_native_seed_sources_have_no_desired_endpoint_premise(self):
        frame=program._frame_source(2,2013)
        self.assertIn('PoseidonCompletion.run_outside',frame)
        self.assertIn('writeBits_preserves',frame)
        self.assertIn('outside_row',frame)
        self.assertEqual(frame.count('#print axioms'),3)
        self.assertNotIn('(satisfied :',frame)
        self.assertNotRegex(frame,r'\b(?:have|let|intro) (?:protected|local)\b|^namespace \w+ :=')
        self.assertIn('preserved column (List.mem_singleton_self column)',frame)
        accepted=dict(boundary=dict(published=(((401,1),),((402,1),))),scalar=dict(value=3),
            checked=dict(parent=dict(constant_copy=200692)),loop=dict(writes=[500,501,700,701]))
        source=program._native_endpoint_source(accepted,2)
        self.assertIn('patchAssignment base',source)
        self.assertIn('theorem published_equal',source)
        self.assertIn('actual_fixed_canonical',source)
        self.assertIn('GroupNativeGenerator.canonical_multiple_inverse',source)
        self.assertIn('(exactOrder : addOrderOf generator = Scalar.order)',source)
        self.assertNotIn('(satisfied :',source)
        self.assertNotIn('(outputRole :',source)
        self.assertNotIn('(publishedRole :',source)
        self.assertNotIn('(pointNonzero :',source)
        self.assertEqual(source.count('#print axioms'),6)
        self.assertEqual(source.count('set_option pp.all true in'),6)
        accepted['boundary']['published']=(((3,1),),((402,1),))
        with self.assertRaises(relation.RelationError):program._native_endpoint_source(accepted,2)

    def test_remaining_legacy_renderer_bytes_equal_retained_authored_source(self):
        # Read-only exact old source already retained before the first factor.
        # This diagnostic comparison is not a generated evidence snapshot.
        path=Path('.work/diagnostics/transfer-implementation-20261002/epk-neutral-renderer-source-01/before/generate_transfer_fixed_spend.py')
        if not path.exists():self.skipTest('diagnostic authored baseline not present')
        spec=importlib.util.spec_from_file_location('circuits._retained_fixed_renderer',path)
        old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
        captures,roles,ordinary=full_fixture(ordered_canonical=True,ordered_fixed=True)
        selections=[fixed.extract_rows(capture,roles,io.BytesIO(ordinary),include_canonical=index==0)
            for index,capture in enumerate(captures)]
        for name,args in [('generate_randomizer_bit_completion',(captures[0],roles,selections[0])),
                ('generate_window_program',(captures[0],roles,selections[0],1)),
                ('generate_chunk',(captures[0],roles,selections[0])),
                ('generate_full',(captures,roles,selections)),
                ('generate_full_completion',(captures,roles,selections))]:
            with self.subTest(name=name):self.assertEqual(getattr(old,name)(*args),getattr(render,name)(*args))


if __name__=='__main__':unittest.main()
