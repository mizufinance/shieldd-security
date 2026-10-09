"""Small constructor-source/fence fixtures; no actual capture/kernel credit."""
import unittest

from circuits import transfer_epk_fixed_sequence as sequence
from circuits import generate_transfer_epk_native_boundary as native
from circuits import transfer_relation as relation


class EpkSequenceTests(unittest.TestCase):
    def test_dual_allocation_fence_retains_only_disjoint_actual_supports(self):
        original={17:(((0,1),(299,7),(1003,2),(200692,3)),((298,1),))}
        actual=sequence._fence(1000,200692,300,1004,{401,1005,27},original)
        self.assertEqual(actual['exceptions'],[27])
        # Native publication at27 is early, so it is excluded, even though
        # the previous ordinary rows are inside both allocation cursors.
        damaged={17:(((27,1),),())}
        with self.assertRaisesRegex(relation.RelationError,'actual prior supports'):
            sequence._fence(1000,200692,300,1004,{401,1005,27},damaged)
        with self.assertRaisesRegex(relation.RelationError,'actual prior supports'):
            sequence._fence(1000,200692,300,1004,{401,1005,27},{17:(((1004,1),),())})
        with self.assertRaisesRegex(relation.RelationError,'bounded32'):
            sequence._fence(1000,200692,300,1004,set(range(33)),{})

    def test_six_native_seeded_cones_have_explicit_inputs_and_original_row_frames(self):
        accepted=dict(protected=[0,1,2,200692]+list(range(3,9)),
            locals=[dict(scalar=dict(value=3+i)) for i in range(6)],
            steps=[dict(fence=dict(origin=1000,copy=200692,low=300+300*i,
                high=1004+600*i,exceptions=[17+i])) for i in range(6)])
        source=sequence._render(accepted)
        self.assertIn('theorem six_cones_complete',source)
        self.assertIn('GroupFrameExceptions.checked_rows',source)
        self.assertIn('change row ∈ prefixRows5 ++ rows5 at member',source)
        self.assertIn('change base 8 = ((n ⟨5,by decide⟩) : F) at inputMeaning',source)
        self.assertIn('parameters : ∀ point ∈',source)
        self.assertIn('(exactOrder : addOrderOf generator = Scalar.order)',source)
        self.assertIn('positive : ∀ scope, 0 < n scope',source)
        self.assertEqual(source.count('#print axioms'),34)
        self.assertEqual(source.count('set_option pp.all true in'),34)
        self.assertNotRegex(source,r'\b(?:def|have|let|intro) (?:protected|local)\b|^namespace \w+ :=')
        self.assertIn('def sharedInputs : List Nat :=',source)
        for forbidden in ('(satisfied :','(outputRole :','(publishedRole :','(pointNonzero :'):
            self.assertNotIn(forbidden,source)

    def test_actual_inverse_and_binding_source_uses_constructed_endpoint(self):
        p=relation.MODULUS;copy=200692
        fixture=dict(scalar=dict(value=3),checked=dict(parent=dict(constant_copy=copy)),
            boundary=dict(published=(((401,1),),((402,1),)),computed=(((501,1),),((502,1),)),
                inverse_constructor=dict(quotient=403,product=504,auxiliary=505,remainder=()),
                inverse_certificate=dict(rows=[1,2,3]),bindings=[dict(rows=[4]),dict(rows=[5])]),
            boundary_raw={0:(((0,1),(copy,p-1)),()),1:(((401,p-1),(403,1)),((505,1),)),
                2:(((401,1),(403,1)),((504,4),(505,1))),3:(((0,p-1),(504,1)),()),
                4:(((401,p-1),(501,1)),()),5:(((402,p-1),(502,1)),())})
        source=native.generate(fixture,0)
        self.assertIn('GroupRowCompletion.extendQuotient',source)
        self.assertIn('have same := ShielddSecurity.RuntimeTransferEpk0FixedNativeEndpoint.published_equal',source)
        self.assertIn('dsimp only at xValue yValue',source)
        self.assertIn('CompilerSignedCompletion.original_rows',source)
        self.assertIn('theorem cone_rows_complete',source)
        self.assertEqual(source.count('#print axioms'),9)
        self.assertEqual(source.count('set_option pp.all true in'),9)
        for forbidden in ('(satisfied :','(pointNonzero :','(inverseValue :','(publishedRole :'):
            self.assertNotIn(forbidden,source)
        # Exact retained copy row is required, including its real sign.
        del fixture['boundary_raw'][0]
        with self.assertRaisesRegex(relation.RelationError,'exact retained copy'):
            native.generate(fixture,0)


if __name__=='__main__':unittest.main()
