"""Source-only neutral rendering and strict ingress; no runtime/kernel credit."""
import copy,hashlib,io,json,unittest
from pathlib import Path
from circuits import generate_transfer_fixed_spend as spend,transfer_fixed_spend as fixed
from circuits import generate_transfer_epk_fixed_completion as generate
from circuits import transfer_epk_fixed_batch as batch,transfer_epk_fixed_canonical as canonical
from circuits import transfer_relation as relation
from tests.fixed_spend_fixture import full_fixture
from tests.test_transfer_epk_fixed_batch import selected_fixture
from tests.test_transfer_epk_fixed_canonical import fixture as canonical_fixture
from tests.test_transfer_epk_fixed import encoded


class NeutralFixedRenderingTests(unittest.TestCase):
    def test_existing_spend_default_bytes_unchanged(self):
        baseline=json.loads(Path(__file__).with_name('fixed_renderer_default_sha256.json').read_text())
        captures,roles,ordinary=full_fixture()
        selected=fixed.extract_rows(captures[0],roles,io.BytesIO(ordinary))
        for key,expected in baseline.items():
            if ':' not in key:continue
            function,offset=key.split(':')
            source=getattr(spend,function)(captures[0],roles,selected,int(offset))
            with self.subTest(key=key):self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),expected)
        captures,roles,ordinary=full_fixture(ordered_canonical=True)
        selected=fixed.extract_rows(captures[0],roles,io.BytesIO(ordinary),include_canonical=True)
        for key,expected in baseline.items():
            if ':' in key:continue
            source=getattr(spend,key)(captures[0],roles,selected)
            with self.subTest(key=key):self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),expected)

    def test_strict_epk_folded_first_and_nonfolded_refusal(self):
        checked,combined,prefixes,(parent,pages,capsules,caller)=selected_fixture()
        extracted=batch._partition(checked,combined,prefixes)
        args=(encoded(parent),pages,capsules,caller,extracted,4)
        sound=generate.generate_window(*args)
        local=generate.generate_window_completion(*args)
        curve=generate.generate_window_complete(*args)
        self.assertIn('RuntimeTransferEpk4FixedWindow000Div',sound)
        self.assertIn('actual_window_coordinates',sound)
        self.assertIn('GroupCircuitCompletion.original_rows_complete',local)
        self.assertIn('RuntimeTransferEpk4FixedWindow000Completion',curve)
        self.assertIn('theorem actual_window_complete',curve)
        self.assertNotIn('(satisfied :',curve)
        self.assertNotIn('(legalX :',curve)
        self.assertNotIn('RuntimeFixedSpend',sound+local+curve)
        self.assertEqual(local.count('#print axioms'),4)
        self.assertEqual(curve.count('#print axioms'),2)
        for invalid in (True,-1,6):
            with self.assertRaises(relation.RelationError):generate.generate_window(*args[:-1],invalid)
        with self.assertRaises(relation.RelationError):generate.generate_window(*args,page_index=7,window_offset=14)
        # Native identity is a positive local algebra fixture. Later windows
        # fold in this fixture, so the real six-product curve template refuses.
        with self.assertRaisesRegex(relation.RelationError,'six exact products'):
            generate.generate_window_complete(*args,window_offset=1)
        for change in ('parent','row','readonly'):
            damaged=copy.deepcopy(extracted);readonly=()
            if change=='parent':damaged['parent_sha256']='f'*64
            elif change=='row':damaged['selected_rows'][1]['b']=[]
            else:readonly=(((262144,1),),)
            with self.subTest(change=change),self.assertRaises(relation.RelationError):
                generate.generate_window_completion(encoded(parent),pages,capsules,caller,damaged,0,readonly_lcs=readonly)

    def test_canonical_native_seed_and_original_assertions_are_constructed(self):
        parents,checked,boundaries,identity,raw,normalized,records=canonical_fixture()
        parent,pages,capsules,caller=parents
        extracted=canonical._derive(checked,boundaries,identity,raw,normalized,records)
        modules=generate.generate_canonical(encoded(parent),pages,capsules,caller,extracted,3)
        complete=modules['RuntimeTransferEpk3CanonicalCompletion']
        order=modules['RuntimeTransferEpk3CanonicalOrder']
        self.assertIn('ScalarRandomizerBounds.bounded_ordered',order)
        self.assertIn('actual_original_rows_complete',complete)
        self.assertIn('ScalarRandomizerCompletion.constructs',complete)
        self.assertIn('(canonical : n < Scalar.order)',complete)
        self.assertIn('(meaning : base 3003 = (n : F))',complete)
        self.assertNotIn('(satisfied :',complete)
        self.assertNotIn('(endpointValue :',complete)
        self.assertNotIn('(pointNonzero :',complete)
        self.assertNotIn('RuntimeFixedSpend',complete+order)
        self.assertEqual(complete.count('#print axioms'),8)
        self.assertIn('theorem bit_reflection',complete)
        self.assertEqual(order.count('#print axioms'),3)
        damaged=copy.deepcopy(extracted);damaged['scopes'][3]['selected_rows'][1]['b']=[]
        with self.assertRaises(relation.RelationError):
            generate.generate_canonical(encoded(parent),pages,capsules,caller,damaged,3)
        with self.assertRaises(relation.RelationError):
            generate.generate_canonical(encoded(parent),pages,capsules,caller,extracted,True)


if __name__=='__main__':unittest.main()
