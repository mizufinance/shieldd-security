"""Mocked maintained CLI/provenance controls; actual ingress tested separately."""
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import security
from tests import test_security as security_tests


class FixedSpendCliTests(unittest.TestCase):
    def test_dependencies_and_full_count_refuse_before_io(self):
        for flags in (['--fixed-spend-inspections','unused'],
                      ['--fixed-spend-inspections',*['unused']*8],
                      ['--fixed-spend-construction-candidates']):
            with patch.object(sys,'argv',['security.py','check',*flags]),contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(security.main(),1)

    def prepare(self,root,*,wrong_addition=False,drift=False,construction=False,subgroup=False):
        from circuits import transfer_fixed_spend as fixed,generate_transfer_fixed_spend as generator
        from circuits import transfer_rk_addition as addition
        original=security.prepare_rnk_hash_candidates
        paths=[root/f'fixed{i}' for i in range(8)]
        for path in paths:path.write_bytes((path.name+'\n').encode())
        for name in fixed.NATIVE_SOURCE_CONTRACT_FILES:
            path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'mocked source snapshot\n')
        identity=dict(relation_digest='a'*64,domain_size=262144,stored_rows=200770)
        checked=[dict(metadata=dict(window_start=i*16,window_count=min(16,126-i*16))) for i in range(8)]
        subgroup_path=root/'subgroup'
        if subgroup:subgroup_path.write_bytes(b'mocked subgroup\n')
        def intercept(args,*a,**kw):
            args.fixed_spend_inspections=paths
            args.fixed_spend_construction_candidates=construction
            args.rk_subgroup_inspection=subgroup_path if subgroup else None
            return original(args,*a,**kw)
        def extract(*a,**kw):
            if drift:paths[-1].write_bytes(b'changed\n')
            return dict(identity=identity)
        with contextlib.ExitStack() as stack:
            if subgroup:
                def prepare_subgroup(path,roles_bytes,roles,addition,joined_identity,relation,write,**kw):
                    self.assertEqual(path,subgroup_path)
                    self.assertEqual(joined_identity,identity)
                    self.assertEqual(kw['construction'],construction)
                    write('RuntimeTransferRkSubgroupCones.lean','import ShielddSecurity.GroupWindows\n')
                stack.enter_context(patch.object(security,'prepare_rk_subgroup_candidates',side_effect=prepare_subgroup))
            stack.enter_context(patch.object(security,'prepare_rnk_hash_candidates',side_effect=intercept))
            stack.enter_context(patch.object(fixed,'inspect_metadata',side_effect=checked))
            stack.enter_context(patch.object(fixed,'join_chunks',return_value=dict(windows=126,chunks=8,scope='mocked coverage')))
            stack.enter_context(patch.object(fixed,'extract_rows',side_effect=extract))
            for name in ('generate_window','generate_chunk','generate_canonical','generate_full'):
                stack.enter_context(patch.object(generator,name,return_value='import ShielddSecurity.GroupFixedChunks\n'))
            if construction:
                for name in ('fixed_completion_join','fixed_completion_bounds_join'):
                    stack.enter_context(patch.object(fixed,name,return_value=dict(scope='mocked structural recipe')))
                for name in ('generate_window_completion','generate_window_complete','generate_randomizer_order',
                             'generate_randomizer_bit_completion','generate_full_completion'):
                    stack.enter_context(patch.object(generator,name,return_value='import ShielddSecurity.GroupFixedCircuitBounds\n'))
                stack.enter_context(patch.object(generator,'generate_window_programs',return_value={
                    f'RuntimeFixedSpendWindow{i:03d}Program':'import ShielddSecurity.GroupFixedCircuitCompletion\n'
                    for i in range(126)}))
                stack.enter_context(patch.object(addition,'generate_whole_completion',return_value='import ShielddSecurity.GroupCircuitCompletion\n'))
            stack.enter_context(patch.object(addition,'extract',return_value=dict(identity=dict(identity,stored_rows=1) if wrong_addition else identity)))
            for name in ('generate','generate_spend_join'):
                stack.enter_context(patch.object(addition,name,return_value='import ShielddSecurity.GroupFixedWindows\n'))
            return security_tests.RnkCandidateManifestTests().prepare(root,with_roles=True)

    def test_manifest_retains_all126_chunks_source_inputs_and_same_assignment_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);result=self.prepare(root)
            manifest=json.loads((root/'candidates/manifest.json').read_text())
            names={Path(record['path']).name for record in manifest['artifacts']}
            self.assertEqual(sum(name.startswith('RuntimeFixedSpendWindow') for name in names),126)
            self.assertEqual(sum(name.startswith('RuntimeFixedSpendChunk') for name in names),8)
            self.assertTrue({'RuntimeTransferRandomizer.lean','RuntimeTransferFixedSpend.lean',
                'RuntimeTransferRkAddition.lean','RuntimeTransferSpendAuthorization.lean',
                'rk-addition-extraction.json','fixed-spend-coverage.json'}<=names)
            self.assertEqual(result['lean_modules'],156)
            inputs={Path(record['path']).name for record in manifest['inputs']}
            self.assertTrue({'transfer_rk_addition.py','generate_transfer_fixed_spend.py','transfer_arithmetic.py'}<=inputs)
            self.assertTrue({f'fixed{i}' for i in range(8)}<=inputs)
            self.assertFalse(manifest['kernel_receipts_reused'])
            self.assertIn('interpretation remain explicit',manifest['native_source_scope'])
            self.assertTrue(any(Path(record['path']).as_posix().endswith('third_party/commonware/codec/src/codec.rs')
                                for record in manifest['inputs']))

    def test_optional_construction_records_source_and_all126_adapters(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);result=self.prepare(root,construction=True)
            manifest=json.loads((root/'candidates/manifest.json').read_text())
            names={Path(record['path']).name for record in manifest['artifacts']}
            self.assertEqual(sum(name.endswith('Program.lean') for name in names),126)
            self.assertTrue({'fixed-spend-completion-ownership.json','fixed-spend-completion-bounds.json',
                'RuntimeFixedSpendRandomizerOrder.lean','RuntimeFixedSpendRandomizerCompletion.lean',
                'RuntimeTransferFixedSpendCompletion.lean','RuntimeTransferRkAdditionCompletion.lean'}<=names)
            self.assertEqual(result['lean_modules'],538)
            inputs={Path(record['path']).name for record in manifest['inputs']}
            self.assertTrue({'GroupFixedCircuitCompletion.lean','GroupFixedCircuitBounds.lean',
                'CompilerSupportPreservation.lean'}<=inputs)
            self.assertFalse(manifest['kernel_receipts_reused'])

    def test_changed_fixed_input_or_addition_identity_never_publishes_manifest(self):
        for kwargs in (dict(drift=True),dict(wrong_addition=True)):
            with tempfile.TemporaryDirectory() as directory:
                root=Path(directory)
                with self.assertRaises(security.CheckError):self.prepare(root,**kwargs)
                self.assertFalse((root/'candidates/manifest.json').exists())

    def test_optional_subgroup_retains_typed_input_and_helper_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);self.prepare(root,subgroup=True)
            manifest=json.loads((root/'candidates/manifest.json').read_text())
            self.assertTrue(manifest['rk_subgroup_candidates'])
            inputs={Path(record['path']).name for record in manifest['inputs']}
            self.assertTrue({'subgroup','transfer_rk_subgroup.py','generate_transfer_rk_subgroup.py',
                'generate_group_cones.py','generate_transfer_rk_sdk.py'}<=inputs)
            self.assertFalse(manifest['kernel_receipts_reused'])


if __name__=='__main__':unittest.main()
