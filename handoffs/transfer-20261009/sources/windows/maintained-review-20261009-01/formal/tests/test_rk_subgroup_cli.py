"""Small optional CLI join controls; mocked rows do not qualify runtime evidence."""
import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import security
from circuits import transfer_rk_subgroup as subgroup
from circuits import generate_transfer_rk_subgroup as generator
from circuits import generate_transfer_rk_sdk as sdk
from circuits import transfer_fixed_spend as fixed
from circuits import generate_transfer_authorization_completion as completion


class RkSubgroupCliTests(unittest.TestCase):
    def test_flag_requires_fixed_roles_before_io(self):
        with patch.object(sys,'argv',['security.py','check','--rk-subgroup-inspection','unused']), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(security.main(),1)

    def prepare(self,*,construction=False,wrong_identity=False):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);capture=root/'subgroup';capture.write_bytes(b'accepted fixture\n')
            rows=root/'rows';rows.write_bytes(b'fixture rows\n')
            identity=dict(relation_digest='a'*64,stored_rows=74,domain_size=256)
            extracted=dict(identity=dict(identity,stored_rows=73) if wrong_identity else identity)
            written={}
            with contextlib.ExitStack() as stack:
                checked=stack.enter_context(patch.object(subgroup,'inspect_metadata',return_value={}))
                replay=stack.enter_context(patch.object(subgroup,'extract',return_value=extracted))
                for name in ('generate_materialization','generate_cones','generate_native_completion'):
                    stack.enter_context(patch.object(generator,name,return_value='diagnostic source'))
                for name in ('generate_owned','generate_full_owned_inputs'):
                    stack.enter_context(patch.object(sdk,name,return_value='diagnostic source'))
                support=stack.enter_context(patch.object(sdk,'generate_support',return_value='diagnostic support'))
                stack.enter_context(patch.object(fixed,'fixed_completion_bounds_join',return_value=dict(high_start=81)))
                coverage=stack.enter_context(patch.object(completion,'generate_fixed_coverage',return_value={
                    f'FixtureFrame{index}':'diagnostic coverage' for index in range(10)}))
                join=stack.enter_context(patch.object(completion,'generate_owned_join',return_value='diagnostic owned join'))
                sources={f'RuntimeFixedSpendWindow{index:03d}':'source fixture' for index in range(126)}
                sources.update({f'RuntimeFixedSpendChunk{start:03d}':'source fixture' for start in range(0,126,16)})
                sources.update(RuntimeTransferRandomizer='source fixture',RuntimeTransferFixedSpend='source fixture')
                security.prepare_rk_subgroup_candidates(capture,b'roles',{'accepted':'fixture'},
                    dict(identity=identity),identity,rows,lambda name,value:written.__setitem__(name,value),
                    captures=[b'fixed'],extractions=[{}],construction=construction,fixed_sources=sources)
                self.assertEqual(checked.call_args.args[:2],(b'accepted fixture\n',{'accepted':'fixture'}))
                self.assertEqual(replay.call_args.args[:2],checked.call_args.args[:2])
                if construction:
                    self.assertEqual(support.call_args.kwargs,dict(high_start=22738))
                    self.assertEqual(set(coverage.call_args.args[0]),set(sources))
                    self.assertTrue(all(isinstance(value,bytes) for value in coverage.call_args.args[0].values()))
                    self.assertEqual(join.call_args.args[3:],(b'roles',dict(identity=identity),b'accepted fixture\n',extracted))
                else:
                    support.assert_not_called();coverage.assert_not_called();join.assert_not_called()
            return written

    def test_optional_soundness_only_emits_two_modules(self):
        written=self.prepare()
        self.assertEqual(sum(name.endswith('.lean') for name in written),2)
        self.assertIn('rk-subgroup-extraction.json',written)

    def test_construction_support_checks_actual_finite_fence_and_same_assignment_join(self):
        written=self.prepare(construction=True)
        self.assertEqual(sum(name.endswith('.lean') for name in written),17)
        self.assertIn('RuntimeTransferOwnedFixedInputs.lean',written)
        self.assertEqual(written['rk-support-scope.json']['high_start'],22738)
        self.assertEqual(written['rk-support-scope.json']['fixed_constructor_high_start'],81)
        self.assertEqual(written['rk-support-scope.json']['support_modules'],10)
        self.assertIn('RuntimeTransferOwnedAuthorizationCompletion.lean',written)
        self.assertIn('remain open',written['rk-support-scope.json']['scope'])

    def test_identity_mismatch_refuses_before_candidate_writes(self):
        with self.assertRaisesRegex(security.CheckError,'ordinary relation identity mismatch'):
            self.prepare(wrong_identity=True)


if __name__=='__main__':unittest.main()
