import json
from pathlib import Path
import tempfile
import unittest
import contextlib
import copy
from types import SimpleNamespace
from unittest.mock import patch
import security

class RelationCliTests(unittest.TestCase):
    def invoke(self, arguments):
        with patch('sys.argv', ['security.py', 'check', *arguments]), patch.object(security, 'check_register', return_value={}):
            return security.main()

    def test_relation_requires_exact_digest(self):
        for extra in ([], ['--expected-relation-digest', 'dev']):
            self.assertEqual(self.invoke(['--relation-export', 'unused', *extra]), 1)

    def test_relation_rejects_qualification_options(self):
        for flag in ('--qualified-receipts', '--candidate-dir', '--publication-observation', '--expected-published-receipt-sha256', '--verify-link'):
            extra = [flag] if flag == '--verify-link' else [flag, 'unused']
            self.assertEqual(self.invoke(['--relation-export', 'unused', '--expected-relation-digest', '0' * 64, *extra]), 1)

    def test_malformed_relation_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rows.jsonl'
            path.write_bytes(b'{"truncated":')
            self.assertEqual(self.invoke(['--relation-export', str(path), '--expected-relation-digest', '0' * 64]), 1)

    def test_canonical_inspection_requires_exact_transport_and_one_kind(self):
        self.assertEqual(self.invoke(['--canonical-balance-inspection', 'unused']), 1)
        self.assertEqual(self.invoke(['--relation-export', 'unused', '--expected-relation-digest', '0'*64,
                                     '--balance-inspection', 'unused', '--canonical-balance-inspection', 'unused']), 1)

    def test_ivk_inspection_requires_transport_and_one_kind(self):
        self.assertEqual(self.invoke(['--ivk-inspection','unused']),1)
        for other in ('--balance-inspection','--canonical-balance-inspection'):
            self.assertEqual(self.invoke(['--relation-export','unused','--expected-relation-digest','0'*64,
                                         '--ivk-inspection','unused',other,'unused']),1)

    def test_reduction_requires_matching_ivk_and_no_qualification(self):
        base=['--relation-export','unused','--expected-relation-digest','0'*64,'--ivk-reduction-inspection','unused']
        self.assertEqual(self.invoke(base),1)
        self.assertEqual(self.invoke(base+['--ivk-inspection','unused','--verify-link']),1)
        self.assertEqual(self.invoke(base+['--ivk-inspection','unused','--balance-inspection','unused']),1)

    def test_reduction_cli_checks_bound_metadata_without_writing(self):
        from circuits import transfer_ivk_rows,transfer_ivk_reduction
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for name in ('ivk','reduction','rows'): (root/name).write_bytes(b'{}\n')
            checked={'selected_rows':[{},{}],'products':[{}],'metadata_sha256':'1'*64,'scope':'diagnostic'}
            with patch.object(transfer_ivk_rows,'inspect_metadata',return_value={'checked':True}) as ingress, \
                 patch.object(transfer_ivk_reduction,'extract',return_value=checked) as extract:
                self.assertEqual(self.invoke(['--relation-export',str(root/'rows'),'--ivk-inspection',str(root/'ivk'),
                    '--ivk-reduction-inspection',str(root/'reduction'),'--expected-relation-digest','0'*64,'--source',str(root)]),0)
                self.assertEqual(ingress.call_args.args[1],root/'crates/crypto/primitives/params')
                self.assertEqual(extract.call_args.args[1],{'checked':True})
            self.assertEqual(sorted(p.name for p in root.iterdir()),['ivk','reduction','rows'])

    def test_ivk_extraction_cli_does_not_promote_evidence(self):
        from circuits import transfer_ivk_rows,hash_rows
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);metadata=root/'metadata';rows=root/'rows'
            metadata.write_bytes(b'{}\n');rows.write_bytes(b'{}\n')
            with patch.object(transfer_ivk_rows,'extract',return_value={}) as extract, \
                 patch.object(hash_rows,'select',return_value={'rows':{1:{},2:{}}}):
                self.assertEqual(self.invoke(['--relation-export',str(rows),'--ivk-inspection',str(metadata),
                    '--expected-relation-digest','0'*64,'--source',str(root)]),0)
                self.assertEqual(extract.call_args.args[2],root/'crates/crypto/primitives/params')
            self.assertEqual(sorted(p.name for p in root.iterdir()),['metadata','rows'])

class AuthorizationRoleCliTests(unittest.TestCase):
    invoke = RelationCliTests.invoke
    def role_args(self):
        return ['--relation-export','unused','--expected-relation-digest','a'*64,
                '--ivk-inspection','unused','--ivk-reduction-inspection','unused',
                '--rnk-dh-inspection','unused','--rnk-hash-inspection','unused',
                '--rnk-hash-candidates-dir','unused','--ownership-cofactor-template','unused',
                '--authorization-roles-inspection','unused']

    def test_roles_require_all_matching_inspections_and_candidates(self):
        self.assertEqual(self.invoke(['--authorization-roles-inspection','unused']),1)
        for flag in ['--ivk-inspection','--ivk-reduction-inspection','--rnk-dh-inspection',
                     '--rnk-hash-inspection','--rnk-hash-candidates-dir','--ownership-cofactor-template']:
            args=self.role_args(); start=args.index(flag); del args[start:start+2]
            with self.subTest(flag=flag): self.assertEqual(self.invoke(args),1)

    def test_roles_refuse_publication_and_mixed_inspections_before_io(self):
        for extra in [['--verify-link'],['--qualified-receipts','unused'],['--candidate-dir','unused'],
                      ['--publication-observation','unused'],['--expected-published-receipt-sha256','a'*64],
                      ['--balance-inspection','unused'],['--ownership-inspection','unused'],
                      ['--ak-subgroup-inspection','unused'],['--handwritten-transfer'],['--exporter-stage','unused']]:
            with self.subTest(extra=extra): self.assertEqual(self.invoke(self.role_args()+extra),1)

    def test_shared_cofactor_flag_still_accepts_ownership_route(self):
        with patch.object(security,'prepare_ownership_candidates',return_value={'scope':'source candidates'}) as prepare:
            self.assertEqual(self.invoke(['--relation-export','unused','--expected-relation-digest','a'*64,
                '--ivk-inspection','unused','--ivk-reduction-inspection','unused','--ownership-chunks',
                *['chunk'+str(i) for i in range(8)],'--ownership-candidates-dir','unused',
                '--ownership-cofactor-template','unused']),0)
        prepare.assert_called_once()
        self.assertEqual(self.invoke(['--ownership-cofactor-template','unused']),1)

    def test_roles_route_passes_matching_accepted_metadata_to_generator(self):
        from circuits import transfer_ivk_rows as ivk,transfer_ivk_reduction as reduction
        from circuits import transfer_ownership as owner,transfer_rnk_hash as rnk,transfer_authorization_roles as roles
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for name in ['rows','ivk','reduction','rnk','hash','roles','cofactor']:
                (root/name).write_bytes((name+'\n').encode())
            shape=dict(domain_size=262144,stored_rows=200770,constant_copy=200692)
            im=dict(shape,handles=[[1,1],[1,2],[1,3],[2,4]])
            rm=dict(shape,remainder_bits=[],remainder=[1,5])
            metadata=dict(domain_size=262144,full_rows=200770,constant_copy=200692,
                          ivk_handles=im['handles'],rnk_bindings={})
            accepted_roles={'metadata':{'scope':'synthetic mocked ingress'}}
            args=['--relation-export',str(root/'rows'),'--expected-relation-digest','a'*64,
                  '--ivk-inspection',str(root/'ivk'),'--ivk-reduction-inspection',str(root/'reduction'),
                  '--rnk-dh-inspection',str(root/'rnk'),'--rnk-hash-inspection',str(root/'hash'),
                  '--authorization-roles-inspection',str(root/'roles'),
                  '--rnk-hash-candidates-dir',str(root/'out'),'--ownership-cofactor-template',str(root/'cofactor')]
            with patch.object(ivk,'inspect_metadata',return_value={'metadata':im}), \
                 patch.object(reduction,'inspect_metadata',return_value={'metadata':rm}), \
                 patch.object(owner,'inspect_rnk_metadata',return_value={'metadata':metadata}), \
                 patch.object(rnk,'inspect_metadata',return_value={'metadata':dict(metadata,block=0)}), \
                 patch.object(rnk,'extract',return_value={}), \
                 patch.object(rnk,'ingress_controls',return_value={'controls':[]}), \
                 patch.object(roles,'inspect_metadata',return_value=accepted_roles) as ingress, \
                 patch.object(security,'prepare_rnk_hash_candidates',return_value={'scope':'diagnostic'}) as prepare:
                self.assertEqual(self.invoke(args),0)
            self.assertEqual(ingress.call_args.args,(b'roles\n','a'*64,im['handles'],metadata,im))
            self.assertEqual(prepare.call_args.kwargs['authorization_bytes'],b'roles\n')
            self.assertIs(prepare.call_args.kwargs['authorization_roles'],accepted_roles)
            self.assertIs(prepare.call_args.kwargs['ivk_metadata'],im)
            self.assertFalse((root/'out').exists())


class RnkCandidateManifestTests(unittest.TestCase):
    """Mocked CLI orchestration/provenance controls; no row or proof qualification."""
    def prepare(self, root, *, drift=False, wrong_rows=False, with_roles=False, wrong_rk_identity=False):
        from circuits import transfer_rnk_hash as rnk,transfer_ownership as owner,transfer_asset_nonzero as asset
        from circuits import generate_hash_round as rounds
        args=SimpleNamespace(source=root,rnk_hash_candidates_dir=root/'candidates',
                             expected_relation_digest='a'*64,authorization_roles_inspection=None)
        for name in ['ivk_inspection','ivk_reduction_inspection','rnk_dh_inspection','rnk_hash_inspection']:
            path=root/name;path.write_bytes(b'{}\n');setattr(args,name,path)
        params=root/'crates/crypto/primitives/params';params.mkdir(parents=True)
        for name in ['poseidon381.json','poseidon381-wide.json']: (params/name).write_bytes(b'{}\n')
        args.relation_export=root/'rows';args.relation_export.write_bytes(b'{}\n')
        args.ownership_cofactor_template=root/'cofactor.json'
        rows=[dict(row=i,a=[[1980,f'{1:064x}']],b=[[1981,f'{1:064x}']]) for i in range(70)]
        rows.append(dict(row=200769,a=[[0,f'{1:064x}'],[200692,f'{asset.P-1:064x}']],b=[]))
        identity=dict(relation_digest='a'*64,domain_size=262144,stored_rows=200770)
        args.ownership_cofactor_template.write_text(json.dumps(dict(identity=identity,selected_rows=rows)))
        metadata=dict(ivk_handles=[],rnk_bindings={},full_rows=200770,domain_size=262144)
        authorization_bytes=authorization_roles=ivk_metadata=None
        if with_roles:
            args.authorization_roles_inspection=root/'roles'
            authorization_bytes=b'roles\n';args.authorization_roles_inspection.write_bytes(authorization_bytes)
            authorization_roles={'metadata':{'scope':'mocked caller boundary'}}
            ivk_metadata={'handles':[],'scope':'mocked accepted IVK'}
        all_blocks=dict(identity=identity,metadata_sha256='b'*64)
        template=dict(identity=identity,row_pairs=[[r['row'],r['row']] for r in rows])
        if wrong_rows: template['row_pairs'][0][1]=42
        registry=dict(identity=identity,point=[[(23,1)],[(24,1)]])
        with contextlib.ExitStack() as stack:
            for name,value in [('extract_all_permutations',all_blocks),('extract_selection',{}),
                               ('extract_ring_selection',{}),('selection_controls',{}),('ingress_controls',{})]:
                stack.enter_context(patch.object(rnk,name,return_value=value))
            stack.enter_context(patch.object(owner,'extract_cofactor_substitutions',return_value=[template,registry]))
            stack.enter_context(patch.object(asset,'inspect',return_value={'identity':identity}))
            stack.enter_context(patch.object(asset,'omission_controls',return_value={}))
            stack.enter_context(patch.object(rnk,'row_permutation_selection',side_effect=lambda *a:
                {'calls':[{'role':'hash'+str(a[2])}]}))
            stack.enter_context(patch.object(rounds,'generate_selected_block',return_value='source'))
            stack.enter_context(patch.object(rounds,'split_block_modules',side_effect=lambda source,prefix:
                [(prefix+'_Data','import ShielddSecurity.RuntimeExternal\n'),
                 (prefix+'_Composition','import ShielddSecurity.'+prefix+'_Data\n')]))
            def selection(*args):
                if drift: (root/'ivk_inspection').write_bytes(b'changed\n')
                return 'import ShielddSecurity.RuntimeExternal\n'
            stack.enter_context(patch.object(rnk,'generate_selection',side_effect=selection))
            for name in ['generate_sponge_join','generate_ring_selection','generate_ring_subgroup_join',
                         'generate_fixed_ring_cofactor','generate_selected_ring_subgroup',
                         'generate_dh_sponge_join','generate_rnk_points_join']:
                stack.enter_context(patch.object(rnk,name,return_value='import ShielddSecurity.RuntimeExternal\n'))
            stack.enter_context(patch.object(owner,'generate_cofactor_substitution',
                return_value='import ShielddSecurity.RuntimeTransferCofactor\n'))
            stack.enter_context(patch.object(asset,'generate',return_value='import ShielddSecurity.Compiler\n'))
            if with_roles:
                from circuits import transfer_rk_binding as rk,transfer_authorization_join as caller
                rk_identity=dict(identity)
                if wrong_rk_identity: rk_identity['stored_rows']=200769
                stack.enter_context(patch.object(rk,'extract',return_value={'identity':rk_identity,'scope':'mocked RK equality'}))
                stack.enter_context(patch.object(rk,'generate',return_value='import ShielddSecurity.Group\n'))
                stack.enter_context(patch.object(caller,'generate_caller_join',return_value='import ShielddSecurity.RuntimeExternal\n'))
            return security.prepare_rnk_hash_candidates(args,b'{}\n',metadata,{},ivk_bytes=b'{}\n',
                reduction_bytes=b'{}\n',rnk_bytes=b'{}\n',authorization_bytes=authorization_bytes,
                authorization_roles=authorization_roles,ivk_metadata=ivk_metadata)

    def test_new_row_candidates_and_external_closure_are_explicit(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);result=self.prepare(root)
            manifest=json.loads((root/'candidates/manifest.json').read_text())
            names={Path(record['path']).name for record in manifest['artifacts']}
            self.assertTrue({'RuntimeRnkRingSelection.lean','RuntimeRegistryRing.lean','RuntimeFixedRing.lean',
                'RuntimeSelectedRing.lean','RuntimeSelectedRingSubgroup.lean','RuntimeRnkJoined.lean',
                'RuntimeRnkPoints.lean','RuntimeTransferAssetNonzero.lean','cofactor-template-replay.json',
                'registry-ring-extraction.json','asset-nonzero-extraction.json','asset-nonzero-controls.json'} <= names)
            self.assertEqual(manifest['lean_modules'],16)
            self.assertEqual(result['lean_modules'],16)
            self.assertFalse(manifest['kernel_receipts_reused'])
            self.assertEqual(manifest['external_dependency_modules'],['Compiler','RuntimeExternal','RuntimeTransferCofactor'])
            self.assertIn('unqualified',manifest['dependency_scope'])
            self.assertEqual(len(manifest['artifacts']),len(list((root/'candidates').iterdir()))-1)

    def test_input_drift_does_not_publish_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            with self.assertRaisesRegex(security.CheckError,'inputs changed'):
                self.prepare(root,drift=True)
            self.assertFalse((root/'candidates/manifest.json').exists())
            self.assertTrue((root/'candidates/RuntimeRegistryRing.lean').exists())

    def test_template_transport_must_preserve_physical_row_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            with self.assertRaisesRegex(security.CheckError,'physical rows changed'):
                self.prepare(root,wrong_rows=True)
            self.assertFalse((root/'candidates/manifest.json').exists())

    def test_optional_roles_add_exact_replayed_rk_binding_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);result=self.prepare(root,with_roles=True)
            manifest=json.loads((root/'candidates/manifest.json').read_text())
            names={Path(record['path']).name for record in manifest['artifacts']}
            self.assertTrue({'RuntimeTransferAuthorizationCaller.lean','RuntimeTransferRkBinding.lean',
                             'rk-binding-extraction.json','authorization-roles-boundaries.json'} <= names)
            self.assertEqual(result['lean_modules'],18)
            self.assertFalse(manifest['kernel_receipts_reused'])
            self.assertIn('Group',manifest['external_dependency_modules'])

    def test_optional_rk_replay_identity_drift_refuses_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            with self.assertRaisesRegex(security.CheckError,'RK binding/RNK ordinary relation identity mismatch'):
                self.prepare(root,with_roles=True,wrong_rk_identity=True)
            self.assertFalse((root/'candidates/manifest.json').exists())
            self.assertFalse((root/'candidates/RuntimeTransferRkBinding.lean').exists())


class AdmissionSourceCliTests(unittest.TestCase):
    invoke = RelationCliTests.invoke

    def test_source_scope_rejects_wrong_command_and_publication_options(self):
        with patch.object(security, 'runtime_identity') as runtime:
            for extra in [['--model-only'], ['--handwritten-transfer'], ['--relation-export', 'unused'],
                          ['--qualified-receipts', 'unused'], ['--candidate-dir', 'unused'],
                          ['--verify-link'], ['--publication-observation', 'unused']]:
                with self.subTest(extra=extra):
                    self.assertEqual(self.invoke(['--scope', 'transfer-admission', *extra]), 1)
            with patch('sys.argv', ['security.py', 'circuits', '--scope', 'transfer-admission']), \
                    patch.object(security, 'check_register', return_value={}):
                self.assertEqual(security.main(), 1)
            runtime.assert_not_called()

    def test_source_scope_remains_read_only_and_unqualified(self):
        import hashlib
        import transfer_coverage as coverage
        metadata = copy.deepcopy(coverage.ADMISSION_SOURCE_FILES)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path, entry in metadata.items():
                raw = ('\n'.join(entry['guards']) + '\n').encode()
                entry['sha256'] = hashlib.sha256(raw).hexdigest()
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            before = {str(p.relative_to(root)): p.read_bytes() for p in root.rglob('*') if p.is_file()}
            with patch.object(coverage, 'ADMISSION_SOURCE_FILES', metadata), \
                    patch.object(security, 'runtime_identity', return_value={'sha': 'a'*40}), \
                    contextlib.redirect_stdout(__import__('io').StringIO()) as output:
                self.assertEqual(self.invoke(['--scope', 'transfer-admission', '--source', str(root)]), 0)
            result = json.loads(output.getvalue())
            self.assertEqual(result['status'], 'source_reviewed_refinement_open')
            self.assertEqual(result['evidence'], [])
            self.assertEqual(result['files'], 43)
            self.assertEqual(before, {str(p.relative_to(root)): p.read_bytes() for p in root.rglob('*') if p.is_file()})


class CurrentTransferPolicyTests(unittest.TestCase):
    def setUp(self):
        self.register=security.read_json(security.ROOT/'assurance.json')

    def check(self):
        original_read=security.read_json
        with patch.object(security,'read_json',side_effect=lambda path:
            self.register if path.name == 'assurance.json' else original_read(path)):
            return security.check_register()

    def test_current_reviewed_mapping_and_open_status_are_preserved(self):
        result=self.check()
        self.assertEqual(result['transfer_assurance']['status'],'open')
        self.assertEqual(result['transfer_assurance']['stage_gates'],{f'T{i}':'open' for i in range(8)})

    def test_nonempty_current_contract_location_target_and_controls_drift_fail(self):
        original=copy.deepcopy(self.register)
        for name in ['current:committed-input','current:action-key','current:patches','current:relation-key']:
            for field,value in [('contract','True'),('runtime_location','historical/Groth16.go'),
                                ('target','historical receipt'),('controls',['compilation failed'])]:
                self.register=copy.deepcopy(original)
                self.register['transfer_assurance']['obligations'][name][field]=value
                with self.subTest(name=name,field=field), self.assertRaisesRegex(security.CheckError,'mapping changed without review'):
                    self.check()

    def test_target_identity_cannot_drift_or_claim_certification(self):
        original=copy.deepcopy(self.register)
        for field,value,message in [('sha','a'*40,'stale current runtime target'),
                                    ('status','certified','unsupported current runtime target certification')]:
            self.register=copy.deepcopy(original)
            self.register['current_runtime_target'][field]=value
            with self.subTest(field=field), self.assertRaisesRegex(security.CheckError,message):
                self.check()

    def test_system_gate_and_backend_assumption_cannot_be_promoted(self):
        original=copy.deepcopy(self.register)
        for claim,message in [('system','system assurance gate'),('backend','explicitly assumed')]:
            for status in ['proved','tested','reviewed']:
                self.register=copy.deepcopy(original)
                self.register['claims'][claim]['status']=status
                with self.subTest(claim=claim,status=status), self.assertRaisesRegex(security.CheckError,message):
                    self.check()


class HandwrittenTransferAuditTests(unittest.TestCase):
    def setUp(self):
        self.module = 'TransferCore'
        self.source = (security.ROOT / 'circuits/ShielddSecurity/TransferCore.lean').read_text()
        self.output = '\n'.join(f"ShielddSecurity.TransferCore.{name} : Nat\n'ShielddSecurity.TransferCore.{name}' does not depend on any axioms"
                                for name in security.TRANSFER_THEOREMS[self.module])

    def test_audit_requires_every_exact_named_statement_and_axiom_report(self):
        security.audit_handwritten_transfer(self.module, self.source, self.output)
        for mutation in [self.output.replace('optional_amount_bounded :', 'missing :'),
                         self.output.replace('does not depend on any axioms', 'depends on axioms: [evil]', 1),
                         self.output + '\nsorryAx', self.output + '\n' + self.output]:
            with self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(self.module, self.source, mutation)

    def test_execution_audit_requires_each_effect_and_rollback_export(self):
        module = 'TransferAdmission'
        source = (security.ROOT / 'circuits/ShielddSecurity/TransferAdmission.lean').read_text()
        names = security.TRANSFER_THEOREMS[module]
        output = '\n'.join(f"ShielddSecurity.{module}.{name} : Nat\n'ShielddSecurity.{module}.{name}' does not depend on any axioms"
                           for name in names)
        security.audit_handwritten_transfer(module, source, output)
        for name in ['exact_transfer_effects', 'ordinary_volume_replay_before_mutation',
                     'fee_funding_no_volume_effects', 'routing_and_index_rollback', 'fee_funding_after_body']:
            with self.subTest(name=name), self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(module, source, output.replace(f'{name} :', 'missing :'))

    def test_source_escape_and_unbounded_budget_rejected(self):
        for mutation in [self.source + '\naxiom bad : False', self.source + '\nexample : True := by sorry',
                         self.source.replace('maxHeartbeats 200000', 'maxHeartbeats 0')]:
            with self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(self.module, mutation, self.output)

    def test_success_consequence_requires_all_nine_named_exports(self):
        module = 'TransferExecution'
        source = (security.ROOT / f'circuits/ShielddSecurity/{module}.lean').read_text()
        names = security.TRANSFER_THEOREMS[module]
        self.assertEqual(len(names), 9)
        output = '\n'.join(f"ShielddSecurity.{module}.{name} : Nat\n'ShielddSecurity.{module}.{name}' does not depend on any axioms"
                           for name in names)
        security.audit_handwritten_transfer(module, source, output)
        for name in names:
            with self.subTest(name=name), self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(module, source, output.replace(f'{name} :', 'missing :'))
        self.assertIn('effectProjection : Item → TransferEffects', source)

    def test_native_projection_audit_requires_each_exact_export(self):
        module = 'TransferProjection'
        source = (security.ROOT / f'circuits/ShielddSecurity/{module}.lean').read_text()
        names = security.TRANSFER_THEOREMS[module]
        self.assertEqual(len(names), 13)
        output = '\n'.join(f"ShielddSecurity.{module}.{name} : Nat\n'ShielddSecurity.{module}.{name}' does not depend on any axioms"
                           for name in names)
        security.audit_handwritten_transfer(module, source, output)
        for name in names:
            with self.subTest(name=name), self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(module, source, output.replace(f'{name} :', 'missing :'))

    def test_ordered_transaction_audit_refuses_missing_or_inexact_exports(self):
        module = 'TransferTransaction'
        source = (security.ROOT / f'circuits/ShielddSecurity/{module}.lean').read_text()
        names = security.TRANSFER_THEOREMS[module]
        self.assertEqual(len(names), 9)
        output = '\n'.join(f"ShielddSecurity.{module}.{name} : Nat\n'ShielddSecurity.{module}.{name}' does not depend on any axioms"
                           for name in names)
        security.audit_handwritten_transfer(module, source, output)
        for name in names:
            with self.subTest(name=name), self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(module, source, output.replace(f'{name} :', 'missing :'))
        for mutation in [output.replace('does not depend on any axioms', 'depends on axioms: [unsafe]', 1),
                         output + '\nerror: failed', output + '\n' + output]:
            with self.assertRaises(security.CheckError):
                security.audit_handwritten_transfer(module, source, mutation)
        with self.assertRaises(security.CheckError):
            security.audit_handwritten_transfer(module, source.replace('maxHeartbeats 250000', 'maxHeartbeats 0'), output)

class IdentityTests(unittest.TestCase):
    def test_duplicate_identity_key_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lock.json"
            path.write_text('{"sha":"a","sha":"b"}')
            with self.assertRaisesRegex(security.CheckError, "duplicate"):
                security.read_json(path)

    def test_branch_name_is_not_a_pin(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_text(json.dumps({"sha":"dev","ref":"dev"}))
            with self.assertRaisesRegex(security.CheckError, "full lowercase"):
                security.locked_sha(root)

    def test_runtime_dirty_or_wrong_commit_rejected(self):
        with patch.object(security, "run", return_value="b" * 40):
            with self.assertRaisesRegex(security.CheckError, "differs"):
                security.runtime_identity(Path.cwd(), "a" * 40)
        with patch.object(security, "run", side_effect=["a" * 40, " M src/lib.rs"]):
            with self.assertRaisesRegex(security.CheckError, "dirty"):
                security.runtime_identity(Path.cwd(), "a" * 40)

    def test_missing_family_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_bytes((security.ROOT / "shieldd.lock").read_bytes())
            register = security.read_json(security.ROOT / "assurance.json")
            del register["families"]["seizure"]
            (root / "assurance.json").write_text(json.dumps(register))
            with self.assertRaisesRegex(security.CheckError, "seven"):
                security.check_register(root)

    def test_failed_promotion_preserves_previous_result(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.json"
            path.write_text('{"old":true}')
            with patch.object(security.os, "replace", side_effect=OSError("blocked")):
                with self.assertRaises(OSError):
                    security.write_result(path, {"new": True})
            self.assertEqual(json.loads(path.read_text()), {"old": True})
            self.assertEqual(list(path.parent.iterdir()), [path])

    def test_required_obligations_cannot_disappear(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_bytes((security.ROOT / "shieldd.lock").read_bytes())
            register = security.read_json(security.ROOT / "assurance.json")
            del register["claims"]["system"]
            (root / "assurance.json").write_text(json.dumps(register))
            with self.assertRaisesRegex(security.CheckError, "required assurance"):
                security.check_register(root)

    def test_family_status_cannot_claim_pilot_certification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "shieldd.lock").write_bytes((security.ROOT / "shieldd.lock").read_bytes())
            register = security.read_json(security.ROOT / "assurance.json")
            register["families"]["transfer"] = "proved"
            (root / "assurance.json").write_text(json.dumps(register))
            with self.assertRaisesRegex(security.CheckError, "whole-family"):
                security.check_register(root)

    def test_adapter_cannot_override_receipt_identity(self):
        identity = {"sha":"a"*40}
        with patch.object(security, "runtime_identity", return_value=identity), patch.object(security, "source_identity", return_value={"dirty": True}), patch.object(Path, "is_file", return_value=True), patch.object(security, "run", return_value='{"outcome":"passed","runtime":{"sha":"forged"},"security":{"dirty":false}}'):
            result = security.execute_pilot("circuits", security.ROOT / ".work/shieldd-current")
        self.assertEqual(result["runtime"], identity)
        self.assertTrue(result["security"]["dirty"])

    def test_source_drift_during_run_discards_result(self):
        with patch.object(security, "runtime_identity", return_value={"sha":"a"*40}), patch.object(security, "source_identity", side_effect=[{"sha256":"before"},{"sha256":"after"}]), patch.object(Path, "is_file", return_value=True), patch.object(security, "run", return_value='{"outcome":"passed"}'):
            with self.assertRaisesRegex(security.CheckError, "changed during"):
                security.execute_pilot("circuits", security.ROOT / ".work/shieldd-current")

    def test_pilot_cannot_name_a_different_checkout_than_cargo(self):
        with self.assertRaisesRegex(security.CheckError, "Cargo dependencies"):
            security.execute_pilot("circuits", Path.cwd())

    def test_timeout_stops_child_process(self):
        import subprocess
        import sys
        import time
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "orphan.txt"
            child = "import time; from pathlib import Path; time.sleep(1.2); Path(" + repr(str(marker)) + ").write_text('orphan')"
            parent = "import subprocess,sys,time; subprocess.Popen([sys.executable,'-c'," + repr(child) + "]); time.sleep(10)"
            with self.assertRaises(subprocess.TimeoutExpired):
                security.run([sys.executable, "-c", parent], timeout=0.3)
            time.sleep(1.3)
            self.assertFalse(marker.exists(), "timed-out verifier left an active child")

    @unittest.skipIf(security.os.name == "nt", "POSIX process-group regression")
    def test_nested_runner_remains_in_outer_timeout_group(self):
        import subprocess
        import sys
        import time
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "orphan.txt"
            child = "import time; from pathlib import Path; time.sleep(1.2); Path(" + repr(str(marker)) + ").write_text('orphan')"
            adapter = "import security,sys; security.run([sys.executable,'-c'," + repr(child) + "], timeout=10, check=False)"
            with self.assertRaises(subprocess.TimeoutExpired):
                security.run([sys.executable, "-c", adapter], timeout=0.3)
            time.sleep(1.3)
            self.assertFalse(marker.exists(), "nested runner escaped outer timeout group")

    def test_expected_semantic_failure_can_be_inspected(self):
        import sys
        result = security.run([sys.executable, "-c", "import sys; print('semantic rejection'); sys.exit(7)"], check=False)
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout.strip(), "semantic rejection")

    def test_model_only_cannot_replace_full_runtime_evidence(self):
        with patch.object(security, 'runtime_identity', return_value={'sha':'a'*40}), patch.object(security, 'source_identity', return_value={'dirty':True}), patch.object(Path, 'is_file', return_value=True), patch.object(security, 'run', return_value='{"outcome":"passed","runtime":null}'):
            with self.assertRaisesRegex(security.CheckError, 'actual runtime evidence'):
                security.execute_pilot('state', security.ROOT / '.work/shieldd-current')
            result = security.execute_pilot('state', security.ROOT / '.work/shieldd-current', model_only=True)
        self.assertEqual(result['pilot'], 'state-model')
        self.assertEqual(result['command'][-1], '--model-only')
