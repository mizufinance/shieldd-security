"""CLI refusal/linkage tests with synthetic reviewed fixtures, never proof evidence."""
from contextlib import contextmanager, ExitStack
import hashlib
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import security
from circuits import check as checker


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TransferSliceTests(unittest.TestCase):
    @contextmanager
    def fixture(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory)
            work = root / '.work'
            work.mkdir()
            runtime = root / 'runtime'
            sources = runtime / 'crates/crypto/circuits/src'
            sources.mkdir(parents=True)
            def write(relative, value):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps(value), encoding='utf-8')
                return {'path': str(path), 'sha256': digest(path)}
            proofs = {}
            for relative in ('circuits/statement_projection.py', 'circuits/ShielddSecurity/TransferStatement.lean',
                             'circuits/ShielddSecurity/PermanentSpend.lean', 'circuits/ShielddSecurity/Rows.lean',
                             'circuits/ShielddSecurity/Range.lean', 'circuits/ShielddSecurity/SpendGateInputs.lean'):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('synthetic fixture only\n')
                proofs[relative] = digest(path)
            runtime_pins = {}
            for name in ('lib.rs', 'transfer.rs', 'encryption.rs', 'audit.rs', 'group.rs', 'note.rs'):
                path = sources / name
                path.write_text('synthetic ' + name)
                runtime_pins[name] = digest(path)
            log = work / 'audit.log'
            log.write_text('\n'.join(name + " : True\n'" + name + "' depends on axioms: [propext]"
                                      for names in security.TRANSFER_SLICE_THEOREMS.values() for name in names))
            logref = {'path': str(log), 'sha256': digest(log)}
            export = write('.work/export.json', {})
            generated = work / 'audited.lean'
            generated.write_bytes(b'synthetic mapping\n')
            artifacts = {'comparison': write('.work/comparison.json', {'runtime_sha': security.TRANSFER_SLICE_SHA,
                           'matched_property': 'permanent-spend-four-gates-v1'})}
            artifacts['decision'] = write('.work/decision.json', {'runtime_sha': security.TRANSFER_SLICE_SHA,
                'chosen_approach': 'direct-lean', 'scope': 'matched permanent-spend four-gate comparison',
                'basis_comparison_sha256': artifacts['comparison']['sha256']})
            for role in ('projection', 'permanent_spend'):
                data = {'runtime_sha': security.TRANSFER_SLICE_SHA, 'scope': role,
                        'theorems': {name: {'full_statement': name + ' : True', 'premises': 'synthetic fixture',
                          'conclusion': 'synthetic fixture', 'log': logref}
                          for name in security.TRANSFER_SLICE_THEOREMS[role]}}
                if role == 'projection':
                    data.update(AST_export=export, audited_generated_source={'path': str(generated), 'sha256': digest(generated)})
                artifacts[role] = write('.work/' + role + '.json', data)
            witnesses = {'boolean': [2,0,2,0,1,0,0], 'selection': [0,0,1,0,0,0,0],
                         'root': [0,0,0,0,0,1,0], 'amount': [1,1,0,0,0,0,0]}
            artifacts['controls'] = write('.work/controls.json', {'runtime_sha': security.TRANSFER_SLICE_SHA,
                'canonical_source_sha256': proofs['circuits/ShielddSecurity/PermanentSpend.lean'],
                'omissions': {name: {'field_modulus': 17, 'assignment_d_a_n_r_s_c_h': value,
                                    'retained_gates': [True,True,True], 'omitted_gate': False,
                                    'independent_BranchSpec': False} for name, value in witnesses.items()},
                'AST_rejections': ['synthetic'] * 6, 'adapter_coordinate_rejections': ['helper coordinate order'],
                'map_rejections': ['synthetic'] * 4})
            artifacts['source_joins'] = write('.work/joins.json', {'runtime_sha': security.TRANSFER_SLICE_SHA,
                'proof_sources': proofs, 'runtime_sources': runtime_pins, 'assumptions': ['synthetic test fixture']})
            qualification = write('.work/qualification.json', {'schema': 'qualified-reduced-transfer-artifacts-v1',
                'runtime_sha': security.TRANSFER_SLICE_SHA, 'scope': 'transfer-slice',
                'acceptance': 'independently_qualified_actual_results', 'artifacts': artifacts, 'raw_refs': [logref]})
            entry = {'schema': 'reduced-transfer-slice-inputs-v1', 'runtime_sha': security.TRANSFER_SLICE_SHA,
                'status': 'blocked', 'policy': 'development_only', 'theorems': security.TRANSFER_SLICE_THEOREMS,
                'scope': 'synthetic fixture', 'limits': ['no proof qualification'], 'assumptions': ['synthetic'],
                'qualification': qualification, 'receipt': {'path': '.work/results/transfer-slice.json', 'sha256': None}}
            write('assurance.json', {'claims': {'system': {'status': 'blocked', 'development_evidence': {'reduced_transfer_slice': entry}}}})
            identity = {'sha': security.TRANSFER_SLICE_SHA}
            inputs = {'version': 'reduced-transfer-proof-inputs-v1', 'sha256': '1' * 64}
            for module in (security, checker):
                stack.enter_context(patch.object(module, 'ROOT', root))
                stack.enter_context(patch.object(module, 'locked_sha', return_value=security.TRANSFER_SLICE_SHA))
                stack.enter_context(patch.object(module, 'check_register', side_effect=lambda: json.loads((root/'assurance.json').read_text())))
                stack.enter_context(patch.object(module, 'runtime_identity', return_value=identity))
                stack.enter_context(patch.object(module, 'source_identity', return_value={'synthetic': True}))
                stack.enter_context(patch.object(module, 'transfer_slice_proof_inputs', return_value=inputs))
            stack.enter_context(patch('circuits.statement_projection.generate', return_value='synthetic mapping\n'))
            yield root, runtime, qualification, entry

    def test_explicit_null_pin_is_not_an_unpinned_observation(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(b'fixture')
            self.assertEqual(security.verified_bytes(path), b'fixture')
            with self.assertRaises(security.CheckError):
                security.verified_bytes(path, None)

    def test_opened_metadata_drift_still_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(b'fixture')
            original = security.os.fstat
            calls = 0
            def changed_after_read(fd):
                nonlocal calls
                result = original(fd)
                calls += 1
                values = {key: getattr(result, key) for key in
                          ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid', 'st_nlink',
                           'st_size', 'st_mtime_ns', 'st_ctime_ns')}
                if calls == 2:
                    values['st_ctime_ns'] += 1
                return SimpleNamespace(**values)
            with patch.object(security.os, 'fstat', side_effect=changed_after_read):
                with self.assertRaisesRegex(security.CheckError, 'opened artifact changed'):
                    security.verified_bytes(path)

    @unittest.skipUnless(security.os.name == 'nt', 'Windows pathname/handle API regression')
    def test_windows_cross_ctime_difference_with_same_identity_is_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(b'fixture')
            original = security.os.fstat
            def different_ctime(fd):
                result = original(fd)
                values = {key: getattr(result, key) for key in
                          ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid', 'st_nlink',
                           'st_size', 'st_mtime_ns', 'st_ctime_ns')}
                values['st_ctime_ns'] = path.lstat().st_ctime_ns + 12345
                return SimpleNamespace(**values)
            with patch.object(security.os, 'fstat', side_effect=different_ctime):
                self.assertEqual(security.verified_bytes(path, digest(path)), b'fixture')

    def test_opened_different_file_identity_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input'
            path.write_bytes(b'fixture')
            original = security.os.fstat
            def different_inode(fd):
                result = original(fd)
                values = {key: getattr(result, key) for key in
                          ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid', 'st_nlink',
                           'st_size', 'st_mtime_ns', 'st_ctime_ns')}
                values['st_ino'] += 1
                return SimpleNamespace(**values)
            with patch.object(security.os, 'fstat', side_effect=different_inode):
                with self.assertRaisesRegex(security.CheckError, 'opened artifact identity changed'):
                    security.verified_bytes(path)

    def test_preregistered_qualification_replacement_refuses(self):
        with self.fixture() as (root, runtime, qualification, entry):
            path = Path(qualification['path'])
            path.write_text(path.read_text() + ' ')
            with self.assertRaises(security.CheckError):
                checker.prepare_transfer_slice(runtime, path, root/'.work/candidate')

    def test_proof_runtime_and_substantive_register_drift_refuse(self):
        for relative in ('circuits/ShielddSecurity/PermanentSpend.lean',
                         'runtime/crates/crypto/circuits/src/note.rs', 'assurance.json'):
            with self.subTest(relative=relative), self.fixture() as (root, runtime, qualification, entry):
                target = root / relative
                original = checker.verified_bytes
                changed = False
                def replace_after_read(path, *args, **kwargs):
                    nonlocal changed
                    value = original(path, *args, **kwargs)
                    if Path(path) == target and not changed:
                        target.write_bytes(target.read_bytes() + b' ')
                        changed = True
                    return value
                with patch.object(checker, 'verified_bytes', side_effect=replace_after_read):
                    with self.assertRaises(security.CheckError):
                        checker.prepare_transfer_slice(runtime, qualification['path'], root/'.work/candidate')

    def test_failed_generation_leaves_previous_atomic_receipt(self):
        with self.fixture() as (root, runtime, qualification, entry):
            receipt = root / '.work/results/transfer-slice.json'
            receipt.parent.mkdir()
            receipt.write_bytes(b'{"previous":true}')
            argv = ['security.py', 'circuits', '--scope', 'transfer-slice', '--source', str(runtime),
                    '--qualified-receipts', qualification['path'], '--candidate-dir', str(root/'.work/candidate')]
            with (patch('circuits.statement_projection.generate', side_effect=security.CheckError('synthetic generation failure')),
                  patch.object(security.sys, 'argv', argv)):
                self.assertEqual(security.main(), 1)
            self.assertEqual(receipt.read_bytes(), b'{"previous":true}')

    def test_replacement_receipt_cannot_pass_expected_sha_even_with_matching_links(self):
        with self.fixture() as (root, runtime, qualification, entry):
            result = checker.prepare_transfer_slice(runtime, qualification['path'], root/'.work/candidate')
            receipt = root / '.work/results/transfer-slice.json'
            receipt.parent.mkdir()
            receipt.write_text(json.dumps(result))
            expected = digest(receipt)
            register = json.loads((root/'assurance.json').read_text())
            register['claims']['system']['development_evidence']['reduced_transfer_slice']['receipt']['sha256'] = expected
            (root/'assurance.json').write_text(json.dumps(register))
            receipt.write_text(receipt.read_text() + ' ')
            with self.assertRaises(security.CheckError):
                security.verify_transfer_slice_link(runtime, root/'.work/observation.json', expected)

    def test_missing_mandatory_raw_capture_refuses(self):
        with self.fixture() as (root, runtime, qualification, entry):
            path = Path(qualification['path'])
            reviewed = json.loads(path.read_text())
            reviewed['raw_refs'].append({'path': str(root/'.work/missing-capture.log'), 'sha256': '0'*64})
            path.write_text(json.dumps(reviewed))
            register = json.loads((root/'assurance.json').read_text())
            register['claims']['system']['development_evidence']['reduced_transfer_slice']['qualification']['sha256'] = digest(path)
            (root/'assurance.json').write_text(json.dumps(register))
            with self.assertRaises((security.CheckError, OSError)):
                checker.prepare_transfer_slice(runtime, path, root/'.work/candidate')

    def test_only_two_derived_links_preserve_normalized_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            register = {'claims': {'system': {'development_evidence': {'reduced_transfer_slice': {
                'scope': 'substantive', 'receipt': {'path': None, 'sha256': None}}}}}}
            (root/'assurance.json').write_text(json.dumps(register))
            (root/'proof.lean').write_text('synthetic proof input')
            with patch.object(security, 'run', return_value='assurance.json\nproof.lean'):
                before = security.transfer_slice_proof_inputs(root)
                entry = register['claims']['system']['development_evidence']['reduced_transfer_slice']
                entry['receipt'] = {'path': '.work/results/transfer-slice.json', 'sha256': '2'*64}
                (root/'assurance.json').write_text(json.dumps(register))
                self.assertEqual(security.transfer_slice_proof_inputs(root), before)
                entry['scope'] = 'changed substantive input'
                (root/'assurance.json').write_text(json.dumps(register))
                self.assertNotEqual(security.transfer_slice_proof_inputs(root), before)


if __name__ == '__main__':
    unittest.main()
