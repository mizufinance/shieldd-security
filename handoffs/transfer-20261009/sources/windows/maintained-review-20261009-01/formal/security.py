#!/usr/bin/env python3
"""Run scoped Shieldd security checks against one exact runtime commit."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
FAMILIES = {"transfer", "reshape1x8", "reshape8x1", "withdrawal", "seizure", "disclosure1", "disclosure32"}

class CheckError(RuntimeError):
    pass

TRANSFER_THEOREMS = {
    'GroupScalarCodec': ['reader_length', 'native_reader_indices', 'low_byte_bit', 'encoded_bit_formula', 'reader_index', 'encoded_reader',
                         'reader_value', 'false_tail_value', 'binary_injective_same_width',
                         'scalar_order_width', 'circuit_field_width', 'canonical_reader_join',
                         'native_field_coordinates', 'native_canonical_coordinates'],
    'TransferCore': ['optional_amount_bounded', 'net_amount_bounded', 'volume_step_preserves_limit',
                     'volume_trace_preserves_limit', 'disclosure_preserves_accumulator', 'inclusive_endpoint'],
    'TransferBalance': ['field_capacity', 'signed_magnitude_sound', 'negative_one_encodings_differ',
                        'field_negative_one_not_group_negative_one', 'effective_scalar_canonical',
                        'negative_zero_scalar', 'negative_one_scalar'],
    'TransferBalanceRows': ['selected_range_sound'],
    'TransferBalanceGroup': ['native_signed_net_agreement', 'action_commitment_sum',
                             'transaction_commitment_decomposition', 'extracted_binding_opening_representation',
                             'nonconservation_exposes_representation_event'],
    'TransferCanonicalBalance': ['checked_committed_canonical'],
    'TransferReduction': ['checked_role_equation', 'checked_inverse_nonzero', 'checked_private_remainder', 'endpoint_append', 'decode_canonical_cast', 'codec_equiv', 'codec_cardinality', 'decoded_reduction'],
    'TransferNativeReduction': ['limb_subtract', 'limb_borrow_equation', 'four_limb_borrow', 'order_limbs', 'final_borrow_select', 'rounds_complete', 'eight_rounds_complete', 'agrees_with_row_reduction', 'accumulator_agreement'],
    'TransferAcceptance': ['every_expected_slot_bound', 'duplicate_slot_fails_closed', 'expected_slots_satisfy_contract', 'delivery_registry_join', 'exact_cache_reuse',
                           'wrong_family_fails_closed', 'wrong_relation_fails_closed', 'exact_public_and_committed_shape',
                           'empty_batch_fails_closed', 'mixed_family_batch_fails_closed', 'wrong_registry_fails_closed', 'wrong_slot_item_fails_closed',
                           'effect_frame_injective', 'effect_equivocation_exposes_collision', 'independent_anchor_join', 'wrong_body_anchor_fails_closed',
                           'proof_bearing_binding_nonidentity', 'identity_requires_canonical_sentinel'],
    'TransferAdmission': ['current_pair_admitted', 'noncurrent_requires_exact_pair', 'zero_grace_disables_history', 'epoch_change_does_not_revive_history', 'grace_endpoint_inclusive',
                          'duplicate_before_mutation', 'pending_respend_before_mutation', 'durable_respend_before_mutation', 'exact_two_spends_staged', 'exact_transfer_effects',
                          'ordinary_volume_replay_before_mutation', 'fee_funding_bypasses_volume_replay', 'ordered_outputs_persist', 'padding_slot_persisted', 'ordinary_volume_effects', 'fee_funding_no_volume_effects', 'duplicate_volume_fails',
                          'run_effects_append', 'fault_after_arbitrary_prefix', 'failed_transaction_restores_snapshot', 'arbitrary_write_boundary_rollback', 'routing_and_index_rollback',
                          'successful_transaction_applies_delta', 'fee_funding_after_body', 'failed_body_never_executes_fee'],
    'TransferLifecycle': ['active_generation_distinct', 'equal_root_exposes_collision', 'admitted_old_snapshot_exposes_collision'],
    'TransferExecution': ['success_requires_spend_ready', 'ordinary_success_requires_volume_fresh', 'successful_transfer_exact',
                          'successful_slots_and_outputs', 'successful_fee_has_no_volume', 'successful_prefix',
                          'successful_body_and_fee_exact', 'body_fee_slot_conflict_rejects', 'accepted_slot_and_successful_effects'],
    'TransferProjection': ['retained_body_exact', 'retained_item_derived', 'projection_preserves_both_slots', 'projection_preserves_volume',
                           'body_slots_length', 'body_slot_order', 'fee_slot_after_body', 'native_slot_count',
                           'duplicate_body_occurrences_preserved', 'wrong_slot_context_refused',
                           'fee_slot_has_only_fixed_spends_outputs', 'retained_action_success_consequence',
                           'admitted_retained_slot_success'],
    'TransferTransaction': ['volume_checked_success_refines', 'routed_slot_success',
                            'routed_slots_success_exact', 'routed_slots_success_contexts',
                            'applied_slots_fields', 'routed_transaction_success_exact',
                            'routed_transaction_success_fields', 'failed_routed_transaction_restores_snapshot',
                            'admitted_routed_transaction_consequence'],
    'TransferSubgroup': ['shared_inverse_affine', 'cofactor_nonidentity'],
    'TransferWindows': ['pair_digits_value', 'variable_loop', 'variable_value', 'fixed_value'],
    'TransferOwnership': ['double_coordinates', 'add_coordinates', 'selected_coordinates', 'window_coordinates', 'precompute_coordinates', 'trace_coordinates', 'trace_scalar_coordinates', 'trace_output_append', 'trace_equations_append'],
    'RowRenaming': ['eval_linear', 'satisfied_row', 'satisfied_rows', 'checked_linear', 'checked_rows'],
    'TransferConservation': ['signed_sum_bound', 'aggregate_bound', 'aggregate_capacity', 'bounded_zero_residue', 'transfer_only_per_asset_conservation', 'selected_fee_bound', 'selected_action_bounds', 'selected_asset_conservation',
                             'signed_sum_append', 'selected_values_append', 'selected_singleton',
                             'optional_fee_funding_once', 'complete_action_count', 'duplicate_action_counted_twice', 'retained_fee_partition',
                             'selected_nonconservation_has_nonzero_residue'],
    'TreeBinding': ['children_preserve_node', 'children_length', 'equal_root_collision', 'framed_root_collision'],
    'TransferSem': ['public_fields_length'],
}

def check_handwritten_transfer_source(module, source):
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', source):
        raise CheckError(f'prohibited proof escape in {module}')
    budgets = re.findall(r'set_option\s+maxHeartbeats\s+(\d+)', source)
    if not budgets or any(not 0 < int(budget) <= 1000000 for budget in budgets):
        raise CheckError(f'finite heartbeat budget required for {module}')

def audit_handwritten_transfer(module, source, output):
    check_handwritten_transfer_source(module, source)
    if 'sorryAx' in output or re.search(r'\berror:', output):
        raise CheckError(f'failed theorem audit for {module}')
    for theorem in TRANSFER_THEOREMS[module]:
        name = f'ShielddSecurity.{module}.{theorem}'
        if not re.search(r'set_option\s+pp\.all\s+true\s+in\s+#check\s+@' + re.escape(theorem) + r'\b', source):
            raise CheckError(f'full signature audit missing in source: {name}')
        if not re.search(r'@?' + re.escape(name) + r'\s*:', output):
            raise CheckError(f'full signature audit missing: {name}')
        reports = re.findall(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", output)
        none = re.findall(r"'" + re.escape(name) + r"' does not depend on any axioms", output)
        if len(reports) + len(none) != 1:
            raise CheckError(f'exact named axiom audit missing: {name}')
        if reports and set(re.findall(r'[\w.]+', reports[0])) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise CheckError(f'nonstandard axiom: {name}')

def check_handwritten_transfer():
    previous = os.environ.get('LEAN_NUM_THREADS')
    os.environ['LEAN_NUM_THREADS'] = '1'
    try:
        for module in TRANSFER_THEOREMS:
            source = ROOT / 'circuits/ShielddSecurity' / f'{module}.lean'
            check_handwritten_transfer_source(module, source.read_text())
        run(['lake', 'build', 'ShielddSecurity.TransferBalanceRows'], cwd=ROOT / 'circuits', timeout=600)
        run(['lake', 'build', 'ShielddSecurity.TransferBalanceGroup'], cwd=ROOT / 'circuits', timeout=300)
        run(['lake', 'build', 'ShielddSecurity.TransferCanonicalBalance'], cwd=ROOT / 'circuits', timeout=300)
        run(['lake', 'build', 'ShielddSecurity.Tree'], cwd=ROOT / 'circuits', timeout=300)
        run(['lake', 'build', 'ShielddSecurity.TransferLifecycle'], cwd=ROOT / 'circuits', timeout=300)
        run(['lake', 'build', 'ShielddSecurity.TransferSubgroup'], cwd=ROOT / 'circuits', timeout=300)
        run(['lake', 'build', 'ShielddSecurity.TransferWindows'], cwd=ROOT / 'circuits', timeout=300)
        run(['lake', 'build', 'ShielddSecurity.TransferTransaction'], cwd=ROOT / 'circuits', timeout=300)
        for module in TRANSFER_THEOREMS:
            source = ROOT / 'circuits/ShielddSecurity' / f'{module}.lean'
            output = run(['lake', 'env', 'lean', '-j1', str(source)], cwd=ROOT / 'circuits', timeout=300)
            print(output)
            audit_handwritten_transfer(module, source.read_text(), output)
        print('Handwritten Transfer theorem audits passed; row/runtime correspondence remains open.')
    finally:
        if previous is None:
            os.environ.pop('LEAN_NUM_THREADS', None)
        else:
            os.environ['LEAN_NUM_THREADS'] = previous

def read_json_bytes(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise CheckError(f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(data.decode('utf-8-sig'), object_pairs_hook=unique)


_OMITTED_EXPECTATION = object()


def verified_bytes(path, expected=_OMITTED_EXPECTATION):
    """One regular-file read for both identity and interpretation; no new authority."""
    path = Path(path)
    before = path.lstat()
    if path.is_symlink() or not stat.S_ISREG(before.st_mode):
        raise CheckError(f'missing or redirected required artifact: {path}')
    fields = ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid', 'st_nlink',
              'st_size', 'st_mtime_ns', 'st_ctime_ns')
    metadata = lambda value, keys=fields: tuple(getattr(value, key) for key in keys)
    # Windows pathname and opened-handle ctime observations can differ even for
    # the same file. Keep each nine-field observation stable through the read;
    # bridge them by the other eight identity fields rather than normalize ctime.
    shared = fields[:-1] if os.name == 'nt' else fields
    with path.open('rb') as handle:
        opened = os.fstat(handle.fileno())
        if metadata(opened, shared) != metadata(before, shared):
            raise CheckError(f'opened artifact identity changed: {path}')
        data = handle.read()
        if metadata(os.fstat(handle.fileno())) != metadata(opened):
            raise CheckError(f'opened artifact changed during read: {path}')
    digest = hashlib.sha256(data).hexdigest()
    if metadata(path.lstat()) != metadata(before):
        raise CheckError(f'artifact changed during read: {path}')
    if expected is not _OMITTED_EXPECTATION and (not isinstance(expected, str)
            or not re.fullmatch(r'[0-9a-f]{64}', expected) or digest != expected):
        raise CheckError(f'predeclared artifact identity mismatch: {path}')
    return data


def read_json(path: Path):
    return read_json_bytes(verified_bytes(path))

def run(command, cwd=ROOT, timeout=60, check=True):
    env = dict(os.environ, GIT_NO_REPLACE_OBJECTS="1")
    # Adapter descendants share the outer verifier's group, so its timeout
    # cannot orphan a nested Cargo/Lean/Java invocation.
    nested = os.environ.get("SHIELDD_SECURITY_PROCESS_GROUP") == "owned"
    env["SHIELDD_SECURITY_PROCESS_GROUP"] = "owned"
    options = {"start_new_session": not nested} if os.name != "nt" else {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP}
    process = subprocess.Popen(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **options)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except (subprocess.TimeoutExpired, KeyboardInterrupt):
        if os.name == "nt":
            stopped = subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"], capture_output=True, timeout=15)
            if stopped.returncode != 0 and process.poll() is None:
                raise CheckError(f"could not terminate verifier process tree {process.pid}; check permissions before starting another job")
        else:
            os.killpg(os.getpgrp() if nested else process.pid, signal.SIGKILL)
        process.wait(timeout=15)
        process.stdout.close()
        process.stderr.close()
        raise
    if not check:
        return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    if process.returncode:
        raise CheckError(f"command failed ({process.returncode}): {command}\n{stdout}{stderr}")
    return stdout.strip()

def locked_sha(root=ROOT):
    lock = read_json(root / "shieldd.lock")
    sha = lock.get("sha", "")
    if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha) or lock.get("ref") != sha:
        raise CheckError("shieldd.lock must select one full lowercase commit SHA")
    if lock.get("repository") != "https://github.com/mizufinance/shieldd.git":
        raise CheckError("unexpected runtime repository")
    return sha

def runtime_identity(source, sha):
    source = Path(source).resolve()
    if run(["git", "rev-parse", "HEAD"], source) != sha:
        raise CheckError("runtime HEAD differs from shieldd.lock")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], source):
        raise CheckError("runtime checkout is dirty; commit or restore runtime changes first")
    return {"sha": sha, "cargo_lock_sha256": hashlib.sha256((source / "Cargo.lock").read_bytes()).hexdigest(),
            "commonware_provenance_sha256": hashlib.sha256((source / "third_party/commonware-patches/provenance.json").read_bytes()).hexdigest()}

def source_identity(root=ROOT):
    # Git's tracked/nonignored file list includes untracked proof sources but excludes caches.
    paths = run(["git", "ls-files", "--cached", "--others", "--exclude-standard"], root).splitlines()
    digest = hashlib.sha256()
    for relative in sorted(set(paths)):
        path = root / relative
        if path.is_file():
            digest.update(relative.encode() + b"\0" + path.read_bytes() + b"\0")
    return {"revision": run(["git", "rev-parse", "HEAD"], root), "sha256": digest.hexdigest(),
            "dirty": bool(run(["git", "status", "--porcelain", "--untracked-files=all"], root))}

def check_register(root=ROOT):
    pin = locked_sha(root)
    register = read_json(root / "assurance.json")
    if set(register.get("families", {})) != FAMILIES:
        raise CheckError("assurance register must enumerate all seven current families")
    if any(value != "blocked" for value in register["families"].values()):
        raise CheckError("whole-family proofs remain blocked in the pilot")
    if register.get("full_system_certification") != "not_established":
        raise CheckError("pilot evidence cannot establish full-system certification")
    runtime_target = register.get('current_runtime_target')
    if not isinstance(runtime_target, dict) or runtime_target.get('sha') != pin:
        raise CheckError('stale current runtime target binding')
    if runtime_target.get('status') != 'source_identified_not_certified':
        raise CheckError('unsupported current runtime target certification')
    claims = register.get("claims")
    if not isinstance(claims, dict) or set(claims) != {"system", "range_volume", "backend", "snapshot_freeze"}:
        raise CheckError("required assurance claims are missing or unknown")
    for name, claim in claims.items():
        if not isinstance(claim, dict):
            raise CheckError(f"claim must be an object: {name}")
        if claim.get("status") not in {"blocked", "proved", "model_checked", "tested", "assumed", "reviewed"}:
            raise CheckError(f"invalid claim status: {name}")
        if not claim.get("scope") or not claim.get("limits"):
            raise CheckError(f"claim lacks scope or limits: {name}")
    if claims['system']['status'] != 'blocked':
        raise CheckError('system assurance gate must remain blocked')
    if claims['backend']['status'] != 'assumed':
        raise CheckError('upstream backend contract must remain explicitly assumed')
    from transfer_coverage import check as check_transfer_coverage, CURRENT
    check_transfer_coverage(register, root, pin, read_json, CheckError)
    # Current-only names are insufficient: preserve their reviewed current
    # contracts and locations instead of accepting a nonempty historical alias.
    obligations = register['transfer_assurance']['obligations']
    for name, (contract, location, target, controls) in CURRENT.items():
        expected = dict(contract=contract, runtime_location=location, target=target, controls=controls)
        if any(obligations[name].get(field) != value for field, value in expected.items()):
            raise CheckError('current Transfer obligation mapping changed without review: ' + name)
    return register

def write_result(path, result):
    """Promote a complete result atomically; failed generation never overwrites it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write("\n")
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def write_ownership_candidate(path, source):
    """Publish fresh diagnostic Lean source; never replace or promote evidence."""
    if path.suffix != '.lean':
        raise CheckError('ownership window candidate requires a fresh .lean path')
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', newline='\n',
                                     dir=path.parent, delete=False) as handle:
        temporary=Path(handle.name)
        handle.write(source)
    try:
        os.link(temporary,path)
    finally:
        temporary.unlink(missing_ok=True)

def prepare_ownership_candidates(args):
    """Replay live-claim source generation; the final manifest is not evidence."""
    generator_files = [ROOT / 'security.py'] + [ROOT / 'circuits' / name for name in (
        'transfer_ownership.py', 'transfer_relation.py', 'transfer_balance_rows.py',
        'transfer_ivk_rows.py', 'transfer_ivk_reduction.py', 'generate_group_cones.py',
        'generate_hash_round.py', 'poseidon_graph.py', 'group_rows.py', 'hash_rows.py',
        'transfer_canonical_balance.py', 'generate_transfer_reduction.py',
        'generate_transfer_ak.py', 'transfer_ak_subgroup.py')]
    generator_inputs = [{'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                        for path in generator_files]
    parameter_path = args.source / 'crates/crypto/primitives/params/poseidon381-wide.json'
    parameter_inputs = [{'path': str(parameter_path.resolve()),
                         'sha256': hashlib.sha256(parameter_path.read_bytes()).hexdigest()}]
    from circuits.transfer_ivk_rows import inspect_metadata as ivk_ingress
    from circuits.transfer_ivk_reduction import inspect_metadata as reduction_ingress
    from circuits.transfer_ownership import (inspect_metadata, match_formulas, join_chunks,
        extract_rows, generate_window_instances, generate_trace_chunk,
        generate_trace_composition, endpoint_controls, extract_cofactor_substitutions,
        generate_cofactor_substitution, generate_sender_ownership_join, generate_ivk_ownership_join,
        joined_sender_endpoint_controls, generate_authorization_ownership_projection)
    if len(args.ownership_chunks) != 8:
        raise CheckError('ownership candidates require eight complete ordered chunks')
    def bounded(path, limit):
        with path.open('rb') as source:
            return source.read(limit + 1)
    ivk_bytes = bounded(args.ivk_inspection, 4 * 2**20)
    reduction_bytes = bounded(args.ivk_reduction_inspection, 2**20)
    ivk = ivk_ingress(ivk_bytes, args.source / 'crates/crypto/primitives/params', args.expected_relation_digest)
    reduction = reduction_ingress(reduction_bytes, ivk, args.expected_relation_digest)['metadata']
    chunks, inputs = [], []
    for path in args.ownership_chunks:
        data = bounded(path, 2 * 2**20)
        chunk = inspect_metadata(data, args.expected_relation_digest, ivk['metadata']['handles'],
                                 reduction['remainder_bits'], reduction['remainder'])
        metadata = chunk['metadata']
        if (metadata['domain_size'] != reduction['domain_size'] or
                metadata['full_rows'] != reduction['stored_rows'] or
                metadata['constant_copy'] != reduction['constant_copy']):
            raise CheckError('ownership/reduction shape or constant-copy mismatch')
        match_formulas(chunk); chunks.append(chunk)
        inputs.append({'path': str(path.resolve()), 'sha256': hashlib.sha256(data).hexdigest(),
                       'start': metadata['window_start'], 'count': metadata['window_count']})
    join_chunks(chunks)
    output = args.ownership_candidates_dir.resolve()
    output.mkdir(parents=False, exist_ok=False)
    extractions, extraction_files = [], []
    def write_json(name, value):
        data = (json.dumps(value, indent=2) + '\n').encode()
        path = output / name
        with path.open('xb') as destination:
            destination.write(data)
        return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest()}
    for position, chunk in enumerate(chunks):
        with args.relation_export.open('rb') as stream:
            extracted = extract_rows(chunk, stream, args.expected_relation_digest, include_bits=True)
        extractions.append(extracted)
        extraction_files.append(write_json(f'extraction-{position:02d}.json', extracted))
    modules, traces = [], []
    for module, source, record in generate_window_instances(chunks, extractions):
        path = output / (module + '.lean')
        write_ownership_candidate(path, source)
        modules.append({'module': module, 'path': str(path), **record})
    for chunk, extracted in zip(chunks, extractions):
        module = f"RuntimeOwnershipTrace{chunk['metadata']['window_start']:03d}"
        source = generate_trace_chunk(chunk, extracted)
        path = output / (module + '.lean')
        write_ownership_candidate(path, source)
        traces.append({'module': module, 'path': str(path),
                       'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
    composition = generate_trace_composition(chunks, extractions)
    composition_path = output / 'RuntimeTransferOwnership.lean'
    write_ownership_candidate(composition_path, composition)
    cofactors = []
    cofactor_input = None
    if args.ownership_cofactor_template:
        template_bytes = bounded(args.ownership_cofactor_template, 2**20)
        if len(template_bytes) > 2**20:
            raise CheckError('cofactor template exceeds bounded input')
        template = json.loads(template_bytes)
        if (not isinstance(template, dict) or not isinstance(template.get('selected_rows'), list)
                or len(template['selected_rows']) != 74
                or any(not isinstance(row, dict) or not isinstance(row.get('a'), list)
                       or not isinstance(row.get('b'), list) for row in template['selected_rows'])):
            raise CheckError('complete typed cofactor template required')
        from circuits import transfer_relation as relation
        for row in template['selected_rows']:
            relation.terms(row['a'], chunks[0]['metadata']['domain_size'])
            relation.terms(row['b'], chunks[0]['metadata']['domain_size'])
        cofactor_input = {'path': str(args.ownership_cofactor_template.resolve()),
                          'sha256': hashlib.sha256(template_bytes).hexdigest()}
        source_columns = {column for row in template['selected_rows']
                          for key in ('a', 'b') for column, _ in row[key]}
        requests = []
        for name, witness_shift, auxiliary_shift, point_name in (
                ('RuntimeSenderDiversified', 476, 15908, 'base'),
                ('RuntimeSenderTransmission', 468, 15842, 'target')):
            mapping = {}
            for column in source_columns:
                if column in (0, chunks[0]['metadata']['constant_copy']): mapping[column] = column
                elif 1980 <= column <= 1987: mapping[column] = column - witness_shift
                elif 49716 <= column <= 49781: mapping[column] = column - auxiliary_shift
                else: raise CheckError('unexpected cofactor template column; candidate shifts are not a proof')
            point = [chunks[0]['derived'][value[1]] for value in chunks[0]['points'][point_name]]
            requests.append({'namespace': name, 'columns': mapping, 'point': point})
        with args.relation_export.open('rb') as stream:
            substituted = extract_cofactor_substitutions(template, requests, stream, args.expected_relation_digest)
        for extracted in substituted:
            source = generate_cofactor_substitution(extracted)
            path = output / (extracted['namespace'] + '.lean')
            write_ownership_candidate(path, source)
            cofactors.append({'module': extracted['namespace'], 'path': str(path),
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
                             'extraction': write_json(extracted['namespace'] + '.json', extracted)})
        from circuits.generate_transfer_reduction import generate_sem_projection_join
        from circuits.generate_transfer_ak import generate_projection_join
        for module, generator in [('RuntimeTransferAuthorization', generate_sem_projection_join),
                                  ('RuntimeTransferAuthorizationAk', generate_projection_join),
                                  ('RuntimeTransferSenderOwnership', generate_sender_ownership_join),
                                  ('RuntimeTransferOwnershipIvk', generate_ivk_ownership_join),
                                  ('RuntimeTransferAuthorizationOwnership', generate_authorization_ownership_projection)]:
            source = generator(); path = output / (module + '.lean')
            write_ownership_candidate(path, source)
            cofactors.append({'module': module, 'path': str(path),
                             'source_sha256': hashlib.sha256(source.encode()).hexdigest()})
    controls = endpoint_controls(chunks, extractions)
    control_file = write_json('endpoint-controls.json', controls)
    joined_control_file = None
    if cofactor_input:
        joined_control_file = write_json('sender-endpoint-controls.json',
            joined_sender_endpoint_controls(chunks, extractions, template, substituted))
    for record in generator_inputs + parameter_inputs + ([cofactor_input] if cofactor_input else []):
        if hashlib.sha256(Path(record['path']).read_bytes()).hexdigest() != record['sha256']:
            raise CheckError('ownership generation source changed during replay')
    manifest = {'schema': 'shieldd-ownership-window-candidates-v1',
        'relation_digest': args.expected_relation_digest, 'inputs': inputs, 'modules': modules,
        'extractions': extraction_files, 'traces': traces, 'endpoint_controls': control_file,
        'composition': {'path': str(composition_path),
                        'source_sha256': hashlib.sha256(composition.encode()).hexdigest()},
        'ivk_metadata_sha256': hashlib.sha256(ivk_bytes).hexdigest(),
        'reduction_metadata_sha256': hashlib.sha256(reduction_bytes).hexdigest(),
        'generator_sha256': hashlib.sha256((ROOT / 'circuits/transfer_ownership.py').read_bytes()).hexdigest(),
        'generator_inputs': generator_inputs,
        'parameter_inputs': parameter_inputs,
        'cofactor_input': cofactor_input, 'cofactor_candidates': cofactors,
        'sender_endpoint_controls': joined_control_file,
        'ordinary_relation_identity_scope': 'strict complete stream verification of the supplied relation digest and framing; no separate raw-file SHA256 claim',
        'scope': 'diagnostic source candidates and selected-row controls only; kernel/trace/full Transfer qualification pending'}
    receipt = write_json('manifest.json', manifest)
    return {'manifest': receipt, 'windows': len(modules), 'trace_chunks': len(traces),
            'control_scope': controls['scope'], 'scope': manifest['scope']}


def prepare_rnk_hash_candidates(args, hash_bytes, rnk_metadata, anchor, *, ivk_bytes, reduction_bytes, rnk_bytes,
                                authorization_bytes=None, authorization_roles=None, ivk_metadata=None):
    """Maintained diagnostic replay; fresh manifest-last output, no gate promotion."""
    from circuits.transfer_rnk_hash import (extract_all_permutations,row_permutation_selection,
        generate_selection,extract_selection,selection_controls,ingress_controls,generate_sponge_join,
        extract_ring_selection,generate_ring_selection,generate_ring_subgroup_join,
        generate_fixed_ring_cofactor,generate_selected_ring_subgroup,generate_dh_sponge_join,
        generate_rnk_points_join)
    from circuits.transfer_ownership import extract_cofactor_substitutions,generate_cofactor_substitution
    from circuits.transfer_authorization_join import FIXED_RING
    from circuits import transfer_relation as relation
    from circuits import transfer_asset_nonzero as asset_rows
    from circuits.generate_hash_round import generate_selected_block,split_block_modules
    files = [ROOT/'security.py']+[ROOT/'circuits'/name for name in (
        'transfer_rnk_hash.py','transfer_ownership.py','transfer_relation.py','transfer_balance_rows.py',
        'transfer_ivk_rows.py','transfer_ivk_reduction.py','transfer_canonical_balance.py',
        'generate_hash_round.py','poseidon_graph.py','hash_rows.py','transfer_asset_nonzero.py',
        'transfer_authorization_roles.py','transfer_authorization_join.py','transfer_rk_binding.py')]
    fixed_paths=getattr(args,'fixed_spend_inspections',None)
    fixed_construction=getattr(args,'fixed_spend_construction_candidates',False)
    subgroup_path=getattr(args,'rk_subgroup_inspection',None)
    if subgroup_path and not fixed_paths:
        raise CheckError('RK subgroup candidates require all eight accepted fixed captures')
    if fixed_construction and not fixed_paths:
        raise CheckError('fixed construction candidates require all eight accepted fixed captures')
    if fixed_paths:
        from circuits.transfer_fixed_spend import NATIVE_SOURCE_CONTRACT_FILES
        if authorization_roles is None or len(fixed_paths)!=8:
            raise CheckError('full fixed spend candidates require accepted authorization roles and eight ordered captures')
        files += list(fixed_paths)
        files += [ROOT/'circuits'/name for name in ('transfer_fixed_spend.py','transfer_arithmetic.py',
            'generate_transfer_fixed_spend.py','generate_transfer_canonical_balance.py','transfer_rk_addition.py',
            'transfer_rk_point_add.py')]
        files += [args.source/name for name in NATIVE_SOURCE_CONTRACT_FILES]
        if fixed_construction:
            files += [ROOT/'circuits/ShielddSecurity'/name for name in (
                'GroupFixedCircuitCompletion.lean','GroupFixedCircuitBounds.lean',
                'CompilerSupportPreservation.lean','GroupCircuitOrder.lean','GroupCircuitCompletion.lean',
                'CompilerLinearCompletion.lean','CompilerCompletion.lean','GroupRowCompletion.lean',
                'ScalarRandomizerCompletion.lean','ScalarRandomizerBounds.lean','ScalarBitReconstruction.lean')]
        if subgroup_path:
            files += [subgroup_path]+[ROOT/'circuits'/name for name in (
                'transfer_rk_subgroup.py','generate_transfer_rk_subgroup.py',
                'generate_group_cones.py','generate_transfer_rk_sdk.py')]
            if fixed_construction:
                files.append(ROOT/'circuits/generate_transfer_authorization_completion.py')
                files += [ROOT/'circuits/ShielddSecurity'/name for name in (
                    'GroupCircuitSupportPreservation.lean','GroupNativeSubgroupWitness.lean',
                    'GroupNativeSdk.lean','GroupNativeSdkPreimage.lean','ShielddScalarReader.lean',
                    'ShielddNativeSdk.lean','ShielddNativeAuthorization.lean',
                    'CompilerFrameCoverage.lean','GroupFrameTransport.lean')]
    files += [args.source/'crates/crypto/primitives/params'/name for name in ('poseidon381.json','poseidon381-wide.json')]
    files += [args.ivk_inspection,args.ivk_reduction_inspection,args.rnk_dh_inspection,args.rnk_hash_inspection]
    if not args.ownership_cofactor_template:
        raise CheckError('RNK hash candidates require an accepted 71-row cofactor template')
    files.append(args.ownership_cofactor_template)
    if bool(authorization_bytes is not None) != bool(authorization_roles is not None):
        raise CheckError('caller candidates require matching accepted role bytes and parser output')
    if authorization_bytes is not None:
        if not isinstance(ivk_metadata,dict):
            raise CheckError('caller/RK candidates require accepted matching IVK metadata')
        files.append(args.authorization_roles_inspection)
    before = [{'path':str(path.resolve()),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()} for path in files]
    for path,data in ((args.ivk_inspection,ivk_bytes),(args.ivk_reduction_inspection,reduction_bytes),
                      (args.rnk_dh_inspection,rnk_bytes),(args.rnk_hash_inspection,hash_bytes)):
        if hashlib.sha256(path.read_bytes()).hexdigest()!=hashlib.sha256(data).hexdigest():
            raise CheckError('RNK hash captured inputs changed before candidate preparation')
    if authorization_bytes is not None and args.authorization_roles_inspection.read_bytes() != authorization_bytes:
        raise CheckError('authorization role bytes changed before candidate preparation')
    with args.ownership_cofactor_template.open('rb') as handle:
        template_bytes = handle.read(2**20 + 1)
    if len(template_bytes) > 2**20:
        raise CheckError('cofactor template exceeds bounded input')
    template = json.loads(template_bytes)
    output = args.rnk_hash_candidates_dir
    if output.exists(): raise CheckError('RNK hash candidates require a fresh output directory')
    output.mkdir(parents=True,exist_ok=False)
    params=args.source/'crates/crypto/primitives/params'
    handles,bindings=rnk_metadata['ivk_handles'],rnk_metadata['rnk_bindings']
    digest=args.expected_relation_digest
    with args.relation_export.open('rb') as stream:
        all_blocks=extract_all_permutations(hash_bytes,stream,params,digest,handles,bindings,anchor)
    with args.relation_export.open('rb') as stream:
        selection=extract_selection(hash_bytes,stream,digest,handles,bindings)
    with args.relation_export.open('rb') as stream:
        ring=extract_ring_selection(hash_bytes,stream,digest,handles,bindings,
            leaf_columns=[23,24],fixed_coordinates=list(FIXED_RING),inverse_column=1991)
    if (not isinstance(template,dict) or not isinstance(template.get('selected_rows'),list)
            or len(template['selected_rows']) != 71):
        raise CheckError('complete typed 71-row cofactor template required')
    for row in template['selected_rows']:
        if not isinstance(row,dict) or set(row) != {'row','a','b'}:
            raise CheckError('malformed cofactor template row')
        relation.natural(row['row'],rnk_metadata['full_rows'])
        for key in ('a','b'): relation.terms(row[key],rnk_metadata['domain_size'])
    source_columns={column for row in template['selected_rows'] for key in ('a','b') for column,_ in row[key]}
    registry_columns={}
    for column in source_columns:
        if column in (0,200692): registry_columns[column]=column
        elif 1980 <= column <= 1986: registry_columns[column]=column-1957
        elif 49716 <= column <= 49779: registry_columns[column]=column-26914
        else: raise CheckError('unexpected cofactor template column; registry shift is only a candidate')
    requests=[dict(namespace='RuntimeTransferCofactorTemplateRows',columns={c:c for c in source_columns},
                   point=[[(1980,1)],[(1981,1)]]),
              dict(namespace='RuntimeRegistryRing',columns=registry_columns,point=[[(23,1)],[(24,1)]])]
    with args.relation_export.open('rb') as stream:
        template_replay,registry=extract_cofactor_substitutions(template,requests,stream,digest,cofactor_only=True)
    if any(left != right for left,right in template_replay['row_pairs']):
        raise CheckError('cofactor template physical rows changed during ordinary replay')
    if template_replay['identity'] != all_blocks['identity'] or registry['identity'] != all_blocks['identity']:
        raise CheckError('registry/cofactor ordinary relation identity mismatch')
    with args.relation_export.open('rb') as stream:
        asset=asset_rows.inspect(stream)
    if asset['identity'] != all_blocks['identity']:
        raise CheckError('asset/RNK ordinary relation identity mismatch')
    records=[]
    generated_sources={}
    def write(name,data):
        path=output/name
        if path.suffix=='.lean':
            write_ownership_candidate(path,data)
            generated_sources[path.stem]=data
        else:
            with path.open('x',encoding='utf-8',newline='\n') as handle:
                handle.write(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
        record={'path':str(path.resolve()),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        records.append(record);return record
    write('anchor-extraction.json',anchor);write('all-permutations-extraction.json',all_blocks)
    write('selection-extraction.json',selection)
    write('ring-selection-extraction.json',ring)
    write('cofactor-template-replay.json',template_replay)
    write('registry-ring-extraction.json',registry)
    write('asset-nonzero-extraction.json',asset)
    write('asset-nonzero-controls.json',asset_rows.omission_controls(asset))
    write('selection-controls.json',selection_controls(hash_bytes,selection,digest,handles,bindings))
    write('ingress-controls.json',ingress_controls(hash_bytes,params,digest,handles,bindings))
    for block in range(3):
        selected=row_permutation_selection(hash_bytes,all_blocks,block,params,digest,handles,bindings)
        source=generate_selected_block({'relation_digest':digest},selected,selected['calls'][0]['role'],0,
                                      all_blocks['metadata_sha256'],permutation_only=True)
        for name,text in split_block_modules(source,'RuntimeRnkHash'+str(block)):write(name+'.lean',text)
    write('RuntimeRnkSelection.lean',generate_selection(hash_bytes,selection,digest,handles,bindings))
    write('RuntimeRnkSponge.lean',generate_sponge_join(hash_bytes,all_blocks,params,digest,handles,bindings))
    write('RuntimeRnkRingSelection.lean',generate_ring_selection(hash_bytes,ring,digest,handles,bindings))
    write('RuntimeRegistryRing.lean',generate_cofactor_substitution(registry,cofactor_only=True))
    for module,generator in (
            ('RuntimeSelectedRing',generate_ring_subgroup_join),('RuntimeFixedRing',generate_fixed_ring_cofactor),
            ('RuntimeSelectedRingSubgroup',generate_selected_ring_subgroup),
            ('RuntimeRnkJoined',generate_dh_sponge_join),('RuntimeRnkPoints',generate_rnk_points_join)):
        write(module+'.lean',generator())
    write('RuntimeTransferAssetNonzero.lean',asset_rows.generate(asset))
    if authorization_roles is not None:
        from circuits.transfer_authorization_join import generate_caller_join
        from circuits.transfer_rk_binding import extract as extract_rk,generate as generate_rk
        with args.relation_export.open('rb') as stream:
            rk=extract_rk(authorization_bytes,stream,digest,handles,rnk_metadata,ivk_metadata)
        if rk['identity'] != all_blocks['identity']:
            raise CheckError('RK binding/RNK ordinary relation identity mismatch')
        write('authorization-roles-boundaries.json',authorization_roles['metadata'])
        write('RuntimeTransferAuthorizationCaller.lean',generate_caller_join(authorization_roles,ring,registry['point']))
        write('rk-binding-extraction.json',rk)
        write('RuntimeTransferRkBinding.lean',generate_rk(authorization_bytes,rk,digest,handles,rnk_metadata,ivk_metadata))
        if fixed_paths:
            from circuits import transfer_fixed_spend as fixed
            from circuits import generate_transfer_fixed_spend as fixed_generator
            captures=[];extractions=[];checked_chunks=[]
            for path in fixed_paths:
                with path.open('rb') as handle:data=handle.read(4*2**20+1)
                checked_chunk=fixed.inspect_metadata(data,authorization_roles)
                checked_chunks.append(checked_chunk);captures.append(data)
            coverage=fixed.join_chunks(checked_chunks)
            for i,(data,chunk) in enumerate(zip(captures,checked_chunks)):
                start=chunk['metadata']['window_start']
                with args.relation_export.open('rb') as stream:
                    extracted=fixed.extract_rows(data,authorization_roles,stream,include_canonical=i==0)
                if extracted['identity'] != all_blocks['identity']:
                    raise CheckError('fixed/RNK ordinary relation identity mismatch')
                extractions.append(extracted)
                write(f'fixed-spend-{start:03d}-metadata.json',chunk['metadata'])
                write(f'fixed-spend-{start:03d}-extraction.json',extracted)
                for offset in range(chunk['metadata']['window_count']):
                    write(f'RuntimeFixedSpendWindow{start+offset:03d}.lean',
                          fixed_generator.generate_window(data,authorization_roles,extracted,offset))
                    if fixed_construction:
                        write(f'RuntimeFixedSpendWindow{start+offset:03d}Completion.lean',
                              fixed_generator.generate_window_completion(data,authorization_roles,extracted,offset))
                        write(f'RuntimeFixedSpendWindow{start+offset:03d}CurveCompletion.lean',
                              fixed_generator.generate_window_complete(data,authorization_roles,extracted,offset))
                write(f'RuntimeFixedSpendChunk{start:03d}.lean',
                      fixed_generator.generate_chunk(data,authorization_roles,extracted))
            write('fixed-spend-coverage.json',dict(windows=coverage['windows'],chunks=coverage['chunks'],scope=coverage['scope']))
            write('RuntimeTransferRandomizer.lean',fixed_generator.generate_canonical(captures[0],authorization_roles,extractions[0]))
            write('RuntimeTransferFixedSpend.lean',fixed_generator.generate_full(captures,authorization_roles,extractions))
            if fixed_construction:
                write('fixed-spend-completion-ownership.json',fixed.fixed_completion_join(captures,authorization_roles,extractions))
                write('fixed-spend-completion-bounds.json',fixed.fixed_completion_bounds_join(captures,authorization_roles,extractions))
                for name,source in fixed_generator.generate_window_programs(captures,authorization_roles,extractions).items():
                    write(name+'.lean',source)
                write('RuntimeFixedSpendRandomizerOrder.lean',fixed_generator.generate_randomizer_order(captures[0],authorization_roles,extractions[0]))
                write('RuntimeFixedSpendRandomizerCompletion.lean',fixed_generator.generate_randomizer_bit_completion(captures[0],authorization_roles,extractions[0]))
                write('RuntimeTransferFixedSpendCompletion.lean',fixed_generator.generate_full_completion(captures,authorization_roles,extractions))
            from circuits import transfer_rk_addition as rk_addition
            addition=rk_addition.extract(authorization_bytes,authorization_roles,lambda:args.relation_export.open('rb'))
            if addition['identity'] != all_blocks['identity']:
                raise CheckError('RK addition/RNK ordinary relation identity mismatch')
            write('rk-addition-extraction.json',addition)
            write('RuntimeTransferRkAddition.lean',rk_addition.generate(authorization_bytes,authorization_roles,addition))
            if fixed_construction:
                write('RuntimeTransferRkAdditionCompletion.lean',rk_addition.generate_whole_completion(authorization_bytes,authorization_roles,addition))
            write('RuntimeTransferSpendAuthorization.lean',rk_addition.generate_spend_join(authorization_bytes,authorization_roles,
                addition,generated_sources['RuntimeTransferAuthorizationCaller']))
            if subgroup_path:
                prepare_rk_subgroup_candidates(subgroup_path,authorization_bytes,authorization_roles,
                    addition,all_blocks['identity'],args.relation_export,write,
                    captures=captures,extractions=extractions,construction=fixed_construction,
                    fixed_sources=generated_sources)
    dependencies=sorted({module for source in generated_sources.values()
                         for module in re.findall(r'^import ShielddSecurity\.(\w+)\s*$',source,re.MULTILINE)}
                        - set(generated_sources))
    for record in before:
        if hashlib.sha256(Path(record['path']).read_bytes()).hexdigest()!=record['sha256']:
            raise CheckError('RNK hash generation inputs changed; no manifest published')
    manifest={'schema':'shieldd-rnk-hash-candidates-v1','relation_identity':all_blocks['identity'],
              'inputs':before,'artifacts':list(records),'permutation_blocks':3,'lean_modules':len(generated_sources),
              'external_dependency_modules':dependencies,
              'dependency_scope':'direct imports outside this bundle only; coherent transitive source/kernel closure remains unqualified',
              'kernel_receipts_reused':False,
              'fixed_construction_candidates':fixed_construction,
              'rk_subgroup_candidates':bool(subgroup_path),
              'construction_scope':'generated source and exact ownership/support recipes only; coherent kernel/native/caller closure remains unqualified',
              'ordinary_relation_scope':'complete digest/framing replay; no separate raw-file SHA claim',
              'scope':'diagnostic candidates and scoped controls; kernel/source/native/full Transfer qualification open'}
    if fixed_paths:
        manifest['native_source_scope']='BE write/LE read/generator source snapshots only; functional primitive and standard-model interpretation remain explicit'
    receipt=write('manifest.json',manifest)
    return {'manifest':receipt,'lean_modules':len(generated_sources),'scope':manifest['scope']}


def prepare_rk_subgroup_candidates(path,authorization_bytes,authorization_roles,addition,identity,
                                   relation_path,write,*,captures,extractions,construction,fixed_sources=None):
    """Typed optional ingress on the same ordinary relation; source candidates only."""
    from circuits import transfer_rk_subgroup as subgroup
    from circuits import generate_transfer_rk_subgroup as generator
    from circuits import generate_transfer_rk_sdk as sdk
    with path.open('rb') as handle:data=handle.read(2**20+1)
    subgroup.inspect_metadata(data,authorization_roles)
    with relation_path.open('rb') as stream:
        extracted=subgroup.extract(data,authorization_roles,stream)
    if extracted['identity'] != identity or addition['identity'] != identity:
        raise CheckError('RK subgroup/addition/RNK ordinary relation identity mismatch')
    write('rk-subgroup-extraction.json',extracted)
    write('RuntimeTransferRkSubgroupMaterialization.lean',generator.generate_materialization(data,authorization_roles,extracted))
    write('RuntimeTransferRkSubgroupCones.lean',generator.generate_cones(data,authorization_roles,extracted))
    if construction:
        from circuits import transfer_fixed_spend as fixed
        from circuits import generate_transfer_authorization_completion as authorization_completion
        if not isinstance(fixed_sources,dict):
            raise CheckError('owned authorization construction requires maintained fixed module sources')
        names={f'RuntimeFixedSpendWindow{index:03d}' for index in range(126)}|{
            f'RuntimeFixedSpendChunk{start:03d}' for start in range(0,126,16)}|{
            'RuntimeTransferRandomizer','RuntimeTransferFixedSpend'}
        if not names <= set(fixed_sources) or any(not isinstance(fixed_sources[name],str) for name in names):
            raise CheckError('owned authorization construction requires all126 maintained fixed row modules')
        support_sources={name:fixed_sources[name].encode('utf8') for name in names}
        bounds=fixed.fixed_completion_bounds_join(captures,authorization_roles,extractions)
        write('RuntimeTransferRkSubgroupCompletion.lean',generator.generate_native_completion(data,authorization_roles,extracted))
        write('RuntimeTransferRkSdkCompletion.lean',sdk.generate_owned(data,authorization_roles,extracted))
        write('RuntimeTransferRkSupport.lean',sdk.generate_support(authorization_bytes,authorization_roles,
            addition,data,extracted,high_start=22738))
        write('RuntimeTransferOwnedFixedInputs.lean',sdk.generate_full_owned_inputs(captures,authorization_roles,extractions))
        for name,source in authorization_completion.generate_fixed_coverage(support_sources).items():
            write(name+'.lean',source)
        write('RuntimeTransferOwnedAuthorizationCompletion.lean',authorization_completion.generate_owned_join(
            captures,authorization_roles,extractions,authorization_bytes,addition,data,extracted))
        write('rk-support-scope.json',dict(high_start=22738,fixed_constructor_high_start=bounds['high_start'],
            support_modules=10,owned_join_exports=2,
            fence_scope='finite actual row/write support fence only; physical compiler origin interpretation separate',
            scope='fixed/randomizer+actual RK addition+public/subgroup+RK binding same-assignment source candidates; earlier IVK/RNK/hash coverage and coherent full Transfer closure remain open'))


def execute_pilot(pilot, source, model_only=False):
    if model_only and pilot != 'state':
        raise CheckError('--model-only applies only to the state command')
    if source.resolve() != (ROOT / ".work/shieldd-current").resolve():
        raise CheckError("pilots require .work/shieldd-current: Cargo dependencies must use the checked runtime")
    runtime = runtime_identity(source, locked_sha())
    security = source_identity()
    adapter = ROOT / pilot / "check.py"
    if not adapter.is_file():
        raise CheckError(f"{pilot} pilot has no executed implementation yet")
    command = [sys.executable, str(adapter), "--source", str(source.resolve())]
    if model_only:
        command.append('--model-only')
    timeout_seconds = 4800 if pilot == 'circuits' else 1800
    payload = json.loads(run(command, timeout=timeout_seconds))
    if payload.get("outcome") != "passed":
        raise CheckError(f"{pilot} did not pass")
    if pilot == 'state' and not model_only and payload.get('runtime') is None:
        raise CheckError('full state replay requires actual runtime evidence')
    if runtime_identity(source, locked_sha()) != runtime or source_identity() != security:
        raise CheckError("verification inputs changed during execution; result discarded")
    return {"pilot": 'state-model' if model_only else pilot, "runtime": runtime, "security": security,
            "command": command, "timeout_seconds": timeout_seconds, "evidence": payload}

TRANSFER_SLICE_SHA = '844389ee069e1fb2e576708842d0b389b4d9a44a'
TRANSFER_SLICE_THEOREMS = {
    'projection': ['ShielddSecurity.RuntimeTransferStatement.projection_exact',
                   'ShielddSecurity.RuntimeTransferStatement.projection_injective'],
    'permanent_spend': ['ShielddSecurity.PermanentSpend.' + name for name in
                        ('branch_sound', 'branch_gates_complete', 'assignment_branch_sound',
                         'required_input_real', 'required_assignment_real')],
}

def transfer_slice_proof_inputs(root=ROOT):
    """Versioned digest; only the two derived register pointers are masked."""
    paths = sorted(set(run(['git', 'ls-files', '--cached', '--others', '--exclude-standard'], root).splitlines()))
    if 'assurance.json' not in paths:
        raise CheckError('assurance register must be a proof input')
    digest = hashlib.sha256()
    for relative in paths:
        path = root / relative
        if not path.is_file():
            continue
        data = path.read_bytes()
        if relative == 'assurance.json':
            register = read_json_bytes(data)
            try:
                receipt = register['claims']['system']['development_evidence']['reduced_transfer_slice']['receipt']
                if set(receipt) != {'path', 'sha256'}:
                    raise CheckError('derived receipt object must have exactly path and sha256')
                for key in ('path', 'sha256'):
                    receipt[key] = '__DERIVED_REDUCED_TRANSFER_RECEIPT__'
            except (KeyError, TypeError) as error:
                raise CheckError('substantive reduced slice entry and both derived pointers must preexist') from error
            data = json.dumps(register, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8')
        digest.update(relative.encode('utf-8') + b'\0' + data + b'\0')
    return {'version': 'reduced-transfer-proof-inputs-v1', 'sha256': digest.hexdigest()}

def prepare_transfer_slice(source, qualification, candidate_dir):
    """Route the named circuit scope through the existing circuit checker."""
    from circuits import check as checker
    try:
        return checker.prepare_transfer_slice(source, qualification, candidate_dir)
    except checker.CheckError as error:
        raise CheckError(str(error)) from error

def verify_transfer_slice_link(source, observation, expected_receipt_sha256):
    """Validate only linkage to an independently retained publication pin."""
    if (not isinstance(expected_receipt_sha256, str)
            or not re.fullmatch(r'[0-9a-f]{64}', expected_receipt_sha256)):
        raise CheckError('an independently retained expected published receipt SHA is required')
    sha = locked_sha()
    if sha != TRANSFER_SLICE_SHA:
        raise CheckError('transfer-slice linkage supports only the exact PR160 lock')
    path = ROOT / '.work/results/transfer-slice.json'
    receipt_bytes = verified_bytes(path, expected_receipt_sha256)
    result = read_json_bytes(receipt_bytes)
    roles = {'comparison', 'decision', 'projection', 'permanent_spend', 'controls', 'source_joins'}
    if (result.get('pilot') != 'transfer-slice'
            or result.get('outcome') != 'qualified_development_artifacts_unlinked'
            or result.get('full_system_certification') != 'not_established'
            or result.get('register_linkage') != 'requires_separate_post_link_validation'
            or result.get('theorems') != TRANSFER_SLICE_THEOREMS
            or result.get('approach') not in {'clean', 'direct-lean'}
            or set(result.get('artifacts', {})) != roles
            or not result.get('assumptions') or not result.get('limits')
            or result.get('raw_pre') != result.get('raw_post')
            or not isinstance(result.get('raw_pre'), dict)
            or result.get('proof_inputs', {}).get('version') != 'reduced-transfer-proof-inputs-v1'):
        raise CheckError('published receipt has wrong narrow pilot/outcome/interface shape')

    def current_inputs():
        register_bytes = verified_bytes(ROOT / 'assurance.json')
        register = read_json_bytes(register_bytes)
        if check_register() != register:
            raise CheckError('register changed during publication observation')
        state = {'runtime': runtime_identity(source, sha),
                 'proof_inputs': transfer_slice_proof_inputs(),
                 'raw_source_post_link': source_identity(),
                 'raw_register_post_link_sha256': hashlib.sha256(register_bytes).hexdigest()}
        verified_bytes(ROOT / 'assurance.json', state['raw_register_post_link_sha256'])
        return state, register

    before, register = current_inputs()
    try:
        entry = register['claims']['system']['development_evidence']['reduced_transfer_slice']
        link = entry['receipt']
        authority_path = str((ROOT / entry['qualification']['path']).resolve())
        authority_sha256 = entry['qualification']['sha256']
    except (KeyError, TypeError) as error:
        raise CheckError('missing predeclared slice linkage/qualification') from error
    if (register['claims']['system']['status'] != 'blocked'
            or link != {'path': '.work/results/transfer-slice.json', 'sha256': expected_receipt_sha256}
            or result['runtime'] != before['runtime']
            or result['proof_inputs'] != before['proof_inputs']
            or result.get('checked_raw_refs', {}).get(authority_path) != authority_sha256):
        raise CheckError('published pinned receipt linkage/runtime/normalized inputs mismatch')
    after, register_after = current_inputs()
    if after != before or register_after != register or verified_bytes(path, expected_receipt_sha256) != receipt_bytes:
        raise CheckError('whole-phase publication inputs or pinned receipt changed')
    observation = Path(observation).resolve()
    if not observation.is_relative_to((ROOT / '.work').resolve()) or observation.exists():
        raise CheckError('fresh publication observation under .work required')
    data = {'scope': 'post-link publication observation only; not requalification or certification',
            'expected_receipt_sha256': expected_receipt_sha256,
            'receipt_sha256': hashlib.sha256(receipt_bytes).hexdigest(),
            **before, 'whole_phase_inputs_equal': True}
    with observation.open('x', encoding='utf-8') as handle:
        json.dump(data, handle, sort_keys=True); handle.write('\n'); handle.flush(); os.fsync(handle.fileno())
    final, final_register = current_inputs()
    if final != before or final_register != register or verified_bytes(path, expected_receipt_sha256) != receipt_bytes:
        raise CheckError('publication inputs drifted after observation write; retain failed observation')
    return data

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "circuits", "state", "release"])
    parser.add_argument("--source", type=Path, default=ROOT / ".work/shieldd-current")
    parser.add_argument('--model-only', action='store_true', help='state finite model only; does not replace runtime replay')
    parser.add_argument('--scope', choices=['legacy', 'transfer-slice', 'transfer-admission'], default='legacy',
                        help='transfer-admission checks reviewed pinned source contracts only; Rust refinement and evidence remain open')
    parser.add_argument('--qualified-receipts', type=Path)
    parser.add_argument('--candidate-dir', type=Path)
    parser.add_argument('--verify-link', action='store_true')
    parser.add_argument('--publication-observation', type=Path)
    parser.add_argument('--expected-published-receipt-sha256', help='independently retained publication SHA; link observation only')
    parser.add_argument('--relation-export', type=Path, help='check serialized Transfer rows only; no semantic/key qualification')
    parser.add_argument('--balance-inspection', type=Path, help='bounded named balance source/row templates; extraction check only')
    parser.add_argument('--canonical-balance-inspection', type=Path, help='bounded canonical blinding row templates; extraction check only')
    parser.add_argument('--ivk-inspection', type=Path, help='bounded current IVK source/hash row extraction; not kernel qualification')
    parser.add_argument('--ivk-reduction-inspection', type=Path, help='bounded IVK reduction rows; requires matching IVK inspection')
    parser.add_argument('--ak-subgroup-inspection', type=Path, help='bounded current AK rows; requires matching IVK inspection; no kernel qualification')
    parser.add_argument('--ownership-inspection', type=Path, help='bounded ownership chunk rows; matching IVK and reduction roles required; no qualification')
    parser.add_argument('--rnk-dh-inspection', type=Path, help='bounded RNK-DH loop rows; matching IVK/reduction required; hash references boundary-only')
    parser.add_argument('--rnk-hash-inspection', type=Path, help='bounded RNK permutation rows; accepted RNK-DH/IVK/reduction roles required; no qualification')
    parser.add_argument('--rnk-hash-candidates-dir', type=Path, help='fresh diagnostic three-permutation/selection candidates from matching RNK captures and ordinary rows')
    parser.add_argument('--authorization-roles-inspection', type=Path, help='bounded caller/spend role LCs; requires matching IVK/reduction/RNK/hash inspections and fresh RNK candidates; no qualification')
    parser.add_argument('--fixed-spend-inspections', nargs='+', type=Path, help='eight ordered accepted fixed captures covering all126 windows; requires accepted roles and fresh RNK candidates; no qualification')
    parser.add_argument('--fixed-spend-construction-candidates', action='store_true', help='additional canonical/window/RK construction source and exact support recipes from all eight fixed captures; pending kernel, no qualification')
    parser.add_argument('--rk-subgroup-inspection', type=Path, help='bounded accepted RK witness/subgroup capture on the same ordinary relation; requires all eight fixed captures; source candidates only')
    parser.add_argument('--ownership-chunks', nargs='+', type=Path, help='eight ordered ownership captures for complete diagnostic window/trace candidates')
    parser.add_argument('--ownership-candidates-dir', type=Path, help='fresh directory for complete ownership candidates and selected-row controls; no evidence promotion')
    parser.add_argument('--ownership-cofactor-template', type=Path, help='accepted complete cofactor rows: 74 for ownership candidates or 71 for RNK hash/registry candidates; ordinary rows are replayed')
    parser.add_argument('--ownership-window-candidate', type=Path, help='fresh diagnostic Lean source for the first observed ownership window; no kernel/evidence promotion')
    parser.add_argument('--ownership-window-offset', type=int, help='bounded offset within observed chunk for a fresh ownership candidate')
    parser.add_argument('--ownership-window-only', action='store_true', help='omit shared precompute proofs from a fresh later-window candidate')
    parser.add_argument('--ownership-first-group-candidate', type=Path, help='fresh first-window bit/group bridge; requires arithmetic candidate and leaves sender base-role join explicit')
    parser.add_argument('--handwritten-transfer', action='store_true', help='compile and audit narrow handwritten lemmas; no evidence promotion')
    parser.add_argument('--exporter-stage', type=Path, help='stage formal-owned exporter bytes in an existing disposable runtime copy; no build or qualification')
    parser.add_argument('--expected-relation-digest', help='independently retained ordinary relation digest for comparison')
    args = parser.parse_args()
    try:
        if bool(args.ownership_chunks) != bool(args.ownership_candidates_dir):
            raise CheckError('complete ownership chunks require a fresh candidates directory')
        if args.ownership_cofactor_template and not (args.ownership_candidates_dir or args.rnk_hash_candidates_dir):
            raise CheckError('cofactor template requires complete ownership or RNK hash candidates')
        if args.authorization_roles_inspection and not (args.ivk_inspection and args.ivk_reduction_inspection
                and args.rnk_dh_inspection and args.rnk_hash_inspection and args.rnk_hash_candidates_dir):
            raise CheckError('authorization roles require matching IVK/reduction/RNK/hash inspections and fresh RNK candidates')
        if args.fixed_spend_inspections and (not args.authorization_roles_inspection or len(args.fixed_spend_inspections)!=8):
            raise CheckError('full fixed spend candidates require accepted authorization roles and eight ordered captures')
        if args.fixed_spend_construction_candidates and not args.fixed_spend_inspections:
            raise CheckError('fixed construction candidates require all eight accepted fixed captures')
        if args.rk_subgroup_inspection and not args.fixed_spend_inspections:
            raise CheckError('RK subgroup candidates require all eight accepted fixed captures')
        if args.rnk_hash_candidates_dir and not args.ownership_cofactor_template:
            raise CheckError('RNK hash candidates require an accepted 71-row cofactor template')
        if (args.ownership_window_offset is not None or args.ownership_window_only or args.ownership_first_group_candidate) and not args.ownership_window_candidate:
            raise CheckError('ownership window offset requires candidate generation')
        if args.model_only and args.command != 'state':
            raise CheckError('--model-only applies only to the state command')
        register = check_register()
        if args.scope == 'transfer-admission':
            if args.command != 'check' or any(value for name, value in vars(args).items()
                    if name not in {'command', 'source', 'scope'}):
                raise CheckError('transfer-admission applies only to check with --source; source review cannot publish or qualify evidence')
            from transfer_coverage import ADMISSION_SOURCE_FILES, inspect_admission_source_contracts
            before = runtime_identity(args.source, locked_sha())
            sources = {path: (args.source / path).read_bytes() for path in ADMISSION_SOURCE_FILES}
            result = inspect_admission_source_contracts(sources, CheckError)
            if (runtime_identity(args.source, locked_sha()) != before or
                    any((args.source / path).read_bytes() != raw for path, raw in sources.items()) or
                    check_register() != register):
                raise CheckError('Transfer admission source/register drifted during review')
            print(json.dumps({'scope': 'Transfer admission source contracts only; no Rust refinement or certification',
                              'runtime': before, **result}, indent=2))
            return 0
        if args.exporter_stage:
            if (args.command != 'check' or args.scope != 'legacy' or args.handwritten_transfer
                    or args.relation_export or args.balance_inspection or args.canonical_balance_inspection
                    or args.ivk_inspection or args.ivk_reduction_inspection or args.ak_subgroup_inspection or args.ownership_inspection or args.rnk_dh_inspection or args.rnk_hash_inspection or args.rnk_hash_candidates_dir or args.authorization_roles_inspection or args.rk_subgroup_inspection or args.ownership_chunks or args.ownership_candidates_dir or args.ownership_window_candidate or args.expected_relation_digest
                    or args.qualified_receipts or args.candidate_dir or args.verify_link
                    or args.publication_observation or args.expected_published_receipt_sha256):
                raise CheckError('exporter staging requires check without proof/inspection/qualification options')
            from integration.staging import prepare_exporters
            try:
                result = prepare_exporters(args.source, args.exporter_stage)
            except (ValueError, OSError) as error:
                raise CheckError(str(error)) from error
            print(json.dumps(result, sort_keys=True))
            return 0
        if args.handwritten_transfer:
            if (args.command != 'check' or args.scope != 'legacy' or args.relation_export or args.balance_inspection or args.canonical_balance_inspection or args.ivk_inspection or args.ivk_reduction_inspection or args.ak_subgroup_inspection or args.ownership_inspection or args.rnk_dh_inspection or args.rnk_hash_inspection or args.rnk_hash_candidates_dir or args.authorization_roles_inspection or args.rk_subgroup_inspection or args.ownership_chunks or args.ownership_candidates_dir or args.ownership_window_candidate
                    or args.expected_relation_digest or args.qualified_receipts or args.candidate_dir
                    or args.verify_link or args.publication_observation or args.expected_published_receipt_sha256):
                raise CheckError('handwritten theorem checks require check without transport/qualification options')
            check_handwritten_transfer()
            return 0
        if args.relation_export or args.expected_relation_digest or args.balance_inspection or args.canonical_balance_inspection or args.ivk_inspection or args.ivk_reduction_inspection or args.ak_subgroup_inspection or args.ownership_inspection or args.rnk_dh_inspection or args.rnk_hash_inspection or args.rnk_hash_candidates_dir or args.authorization_roles_inspection or args.rk_subgroup_inspection or args.ownership_chunks or args.ownership_candidates_dir or args.ownership_window_candidate:
            if (args.qualified_receipts or args.candidate_dir or args.verify_link
                    or args.publication_observation or args.expected_published_receipt_sha256):
                raise CheckError('relation inspection cannot process qualification or publication options')
            if (args.command != 'check' or args.scope != 'legacy' or not args.relation_export
                    or not args.expected_relation_digest or not re.fullmatch(r'[0-9a-f]{64}', args.expected_relation_digest)):
                raise CheckError('relation inspection requires check, exported rows and an exact expected digest')
            if sum(bool(value) for value in (args.balance_inspection,args.canonical_balance_inspection,args.ivk_inspection)) > 1:
                raise CheckError('select one bounded inspection kind per run')
            if args.ownership_chunks:
                if (args.ownership_inspection or args.rnk_dh_inspection or args.rnk_hash_inspection or args.rnk_hash_candidates_dir or args.authorization_roles_inspection or args.rk_subgroup_inspection or args.ownership_window_candidate or args.ak_subgroup_inspection
                        or args.balance_inspection or args.canonical_balance_inspection
                        or not args.ivk_inspection or not args.ivk_reduction_inspection):
                    raise CheckError('complete ownership candidates require matching IVK/reduction without mixed slices')
                result = prepare_ownership_candidates(args)
                print(json.dumps(result, sort_keys=True))
                return 0
            if args.ownership_window_candidate and not args.ownership_inspection:
                raise CheckError('ownership window candidate requires ownership inspection')
            if args.rnk_hash_candidates_dir and not args.rnk_hash_inspection:
                raise CheckError('RNK hash candidates require RNK hash inspection')
            if args.rnk_hash_inspection and not args.rnk_dh_inspection:
                raise CheckError('RNK hash inspection requires matching RNK-DH inspection')
            if args.rnk_dh_inspection:
                if (not args.ivk_inspection or not args.ivk_reduction_inspection
                        or args.ownership_inspection or args.ownership_chunks or args.ownership_window_candidate
                        or args.ak_subgroup_inspection or args.balance_inspection or args.canonical_balance_inspection):
                    raise CheckError('RNK-DH inspection requires matching IVK/reduction without mixed slices')
                from circuits.transfer_ivk_rows import inspect_metadata as inspect_ivk
                from circuits.transfer_ivk_reduction import inspect_metadata as inspect_reduction
                from circuits.transfer_ownership import inspect_rnk_metadata, extract_rows
                with args.ivk_inspection.open('rb') as handle:ivk_bytes=handle.read(4*2**20+1)
                with args.ivk_reduction_inspection.open('rb') as handle:reduction_bytes=handle.read(2**20+1)
                with args.rnk_dh_inspection.open('rb') as handle:rnk_bytes=handle.read(2*2**20+1)
                ivk=inspect_ivk(ivk_bytes,args.source / 'crates/crypto/primitives/params',args.expected_relation_digest)
                reduction=inspect_reduction(reduction_bytes,ivk,args.expected_relation_digest)
                rm=reduction['metadata']
                observed=inspect_rnk_metadata(rnk_bytes,args.expected_relation_digest,
                    ivk['metadata']['handles'],rm['remainder_bits'],rm['remainder'])
                metadata=observed['metadata']
                if (metadata['domain_size']!=rm['domain_size'] or metadata['full_rows']!=rm['stored_rows']
                        or metadata['constant_copy']!=rm['constant_copy']):
                    raise CheckError('RNK-DH/reduction shape or constant-copy mismatch')
                if args.rnk_hash_inspection:
                    from circuits.transfer_rnk_hash import inspect_metadata as inspect_hash, extract, ingress_controls
                    with args.rnk_hash_inspection.open('rb') as handle:hash_bytes=handle.read(4*2**20+1)
                    hash_state=inspect_hash(hash_bytes,args.source / 'crates/crypto/primitives/params',
                        args.expected_relation_digest,metadata['ivk_handles'],metadata['rnk_bindings'])
                    hm=hash_state['metadata']
                    if (hm['domain_size']!=rm['domain_size'] or hm['full_rows']!=rm['stored_rows']
                            or hm['constant_copy']!=rm['constant_copy']):
                        raise CheckError('RNK hash/reduction shape or constant-copy mismatch')
                    with args.relation_export.open('rb') as stream:
                        checked=extract(hash_bytes,stream,args.source / 'crates/crypto/primitives/params',
                            args.expected_relation_digest,metadata['ivk_handles'],metadata['rnk_bindings'])
                    controls=ingress_controls(hash_bytes,args.source / 'crates/crypto/primitives/params',
                        args.expected_relation_digest,metadata['ivk_handles'],metadata['rnk_bindings'])
                    authorization_bytes=authorization_roles=None
                    if args.authorization_roles_inspection:
                        from circuits.transfer_authorization_roles import inspect_metadata as inspect_roles
                        with args.authorization_roles_inspection.open('rb') as handle:
                            authorization_bytes=handle.read(2*2**20+1)
                        authorization_roles=inspect_roles(authorization_bytes,args.expected_relation_digest,
                            metadata['ivk_handles'],metadata,ivk['metadata'])
                    if args.rnk_hash_candidates_dir:
                        result=prepare_rnk_hash_candidates(args,hash_bytes,metadata,checked,
                            ivk_bytes=ivk_bytes,reduction_bytes=reduction_bytes,rnk_bytes=rnk_bytes,
                            authorization_bytes=authorization_bytes,authorization_roles=authorization_roles,
                            ivk_metadata=ivk['metadata'])
                        print(json.dumps(result,sort_keys=True))
                        return 0
                    result={'relation_digest':args.expected_relation_digest,'selected_rows':len(checked['selected_rows']),
                            'products':len(checked['products']),'block':hm['block'],
                            'metadata_sha256':checked['metadata_sha256'],'ingress_controls':len(controls['controls']),
                            'scope':'RNK permutation extraction/control only; kernel/sponge/Transfer qualification open'}
                else:
                    with args.relation_export.open('rb') as stream:
                        checked=extract_rows(observed,stream,args.expected_relation_digest,include_bits=True)
                    result={'relation_digest':args.expected_relation_digest,'selected_rows':len(checked['selected_rows']),
                            'products':len(checked['products']),'window_start':metadata['window_start'],
                            'window_count':metadata['window_count'],'metadata_sha256':hashlib.sha256(rnk_bytes).hexdigest(),
                            'scope':'RNK-DH loop extraction only; hash boundary refs, group/source/kernel qualification open'}
            elif args.ownership_inspection:
                if (not args.ivk_inspection or not args.ivk_reduction_inspection
                        or args.ak_subgroup_inspection or args.balance_inspection or args.canonical_balance_inspection):
                    raise CheckError('ownership inspection requires matching IVK and reduction inspection only')
                from circuits.transfer_ivk_rows import inspect_metadata as inspect_ivk
                from circuits.transfer_ivk_reduction import inspect_metadata as inspect_reduction
                from circuits.transfer_ownership import inspect_metadata, extract_rows, generate_window_equations, generate_first_group_window
                with args.ivk_inspection.open('rb') as metadata:
                    ivk_bytes=metadata.read(4*2**20+1)
                with args.ivk_reduction_inspection.open('rb') as metadata:
                    reduction_bytes=metadata.read(2**20+1)
                with args.ownership_inspection.open('rb') as metadata:
                    ownership_bytes=metadata.read(2*2**20+1)
                parameters=args.source / 'crates/crypto/primitives/params'
                ivk=inspect_ivk(ivk_bytes,parameters,args.expected_relation_digest)
                reduction=inspect_reduction(reduction_bytes,ivk,args.expected_relation_digest)
                rm=reduction['metadata']
                observed=inspect_metadata(ownership_bytes,args.expected_relation_digest,
                    ivk['metadata']['handles'],rm['remainder_bits'],rm['remainder'])
                om=observed['metadata']
                if (om['domain_size']!=rm['domain_size'] or om['full_rows']!=rm['stored_rows']
                        or om['constant_copy']!=rm['constant_copy']):
                    raise CheckError('ownership/reduction shape or constant-copy mismatch')
                with args.relation_export.open('rb') as stream:
                    checked=extract_rows(observed,stream,args.expected_relation_digest,
                                         include_bits=True) if args.ownership_first_group_candidate else extract_rows(observed,stream,args.expected_relation_digest)
                result={'relation_digest':args.expected_relation_digest,
                        'selected_rows':len(checked['selected_rows']),'products':len(checked['products']),
                        'window_start':observed['metadata']['window_start'],
                        'window_count':observed['metadata']['window_count'],
                        'metadata_sha256':hashlib.sha256(ownership_bytes).hexdigest(),
                        'scope':checked['scope']}
                if args.ownership_window_candidate:
                    offset=0 if args.ownership_window_offset is None else args.ownership_window_offset
                    if not 0 <= offset < observed['metadata']['window_count']:
                        raise CheckError('ownership window offset outside observed chunk')
                    global_window=observed['metadata']['window_start']+offset
                    namespace=f'RuntimeOwnershipWindow{global_window:03d}'
                    group_candidate=None
                    if args.ownership_first_group_candidate:
                        if global_window!=0 or args.ownership_window_only:
                            raise CheckError('first ownership group candidate requires complete window zero arithmetic')
                        group_candidate=generate_first_group_window(observed,checked,
                            arithmetic_module=args.ownership_window_candidate.stem,
                            arithmetic_namespace=namespace)
                    options={'include_precompute':False} if args.ownership_window_only else {}
                    candidate=generate_window_equations(observed,checked,result['metadata_sha256'],
                                                       window_offset=offset,namespace=namespace,**options)
                    write_ownership_candidate(args.ownership_window_candidate,candidate)
                    result['candidate_window']=global_window
                    result['candidate_namespace']='ShielddSecurity.'+namespace
                    result['candidate_includes_precompute']=not args.ownership_window_only
                    result['candidate_source_sha256']=hashlib.sha256(candidate.encode('utf-8')).hexdigest()
                    result['candidate_source']=str(args.ownership_window_candidate.resolve())
                    result['candidate_scope']='generated arithmetic candidate only; kernel/source/group/full Transfer qualification pending'
                    if group_candidate is not None:
                        write_ownership_candidate(args.ownership_first_group_candidate,group_candidate)
                        result['group_candidate_source']=str(args.ownership_first_group_candidate.resolve())
                        result['group_candidate_source_sha256']=hashlib.sha256(group_candidate.encode('utf-8')).hexdigest()
                        result['group_candidate_scope']='actual bits/group candidate; global model/codec and sender base-role join explicit; no kernel/evidence promotion'
            elif args.ak_subgroup_inspection:
                if not args.ivk_inspection or args.ivk_reduction_inspection or args.balance_inspection or args.canonical_balance_inspection:
                    raise CheckError('AK subgroup inspection requires matching IVK inspection only')
                from circuits.transfer_ivk_rows import inspect_metadata
                from circuits.transfer_ak_subgroup import extract, ingress_controls, scoped_semantic_controls
                with args.ivk_inspection.open('rb') as metadata:
                    ivk_bytes = metadata.read(4*2**20+1)
                with args.ak_subgroup_inspection.open('rb') as metadata:
                    ak_bytes = metadata.read(2**20+1)
                ivk = inspect_metadata(ivk_bytes,args.source / 'crates/crypto/primitives/params',args.expected_relation_digest)
                with args.relation_export.open('rb') as stream:
                    checked = extract(ak_bytes,ivk['metadata']['handles'],stream,args.expected_relation_digest)
                ingress = ingress_controls(ak_bytes,ivk['metadata']['handles'],args.expected_relation_digest)
                controls = scoped_semantic_controls(ak_bytes,checked,ivk['metadata']['handles'],args.expected_relation_digest)
                result = {'relation_digest':args.expected_relation_digest,'selected_rows':len(checked['selected_rows']),
                          'products':len(checked['products']),'metadata_sha256':checked['metadata_sha256'],
                          'ingress_controls':len(ingress['cases']),
                          'semantic_omissions':sum(case['omitted_original_row'] is not None for case in controls['cases']),
                          'positive_cases':sum(case['omitted_original_row'] is None for case in controls['cases']),
                          'scope':checked['scope'],'control_scope':controls['scope']}
            elif args.ivk_reduction_inspection:
                if not args.ivk_inspection or args.balance_inspection or args.canonical_balance_inspection:
                    raise CheckError('reduction inspection requires matching IVK inspection only')
                from circuits.transfer_ivk_rows import inspect_metadata
                from circuits.transfer_ivk_reduction import extract
                with args.ivk_inspection.open('rb') as metadata:
                    ivk_bytes=metadata.read(4*2**20+1)
                with args.ivk_reduction_inspection.open('rb') as metadata:
                    reduction_bytes=metadata.read(2**20+1)
                parameters=args.source / 'crates/crypto/primitives/params'
                ivk=inspect_metadata(ivk_bytes,parameters,args.expected_relation_digest)
                with args.relation_export.open('rb') as stream:
                    checked=extract(reduction_bytes,ivk,stream,args.expected_relation_digest)
                result={'relation_digest':args.expected_relation_digest,
                        'selected_rows':len(checked['selected_rows']), 'products':len(checked['products']),
                        'metadata_sha256':checked['metadata_sha256'],'scope':checked['scope']}
            elif args.ivk_inspection:
                from circuits.transfer_ivk_rows import extract
                from circuits.hash_rows import select
                with args.ivk_inspection.open('rb') as metadata:
                    metadata_bytes = metadata.read(4*2**20+1)
                parameter_root = args.source / 'crates/crypto/primitives/params'
                with args.relation_export.open('rb') as stream:
                    exported = extract(metadata_bytes,stream,parameter_root,args.expected_relation_digest)
                selected = select(exported,parameter_root)
                result = {'relation_digest':args.expected_relation_digest,
                    'selected_rows':len(selected['rows']), 'rounds':65,
                    'role':'authorization.ivk',
                    'scope':'current source/row template extraction only; kernel, role interpretation and full Transfer joins open'}
            elif args.canonical_balance_inspection:
                from circuits.transfer_canonical_balance import inspect
                with args.canonical_balance_inspection.open('rb') as metadata:
                    metadata_bytes = metadata.read(2**20 + 1)
                with args.relation_export.open('rb') as stream:
                    result = inspect(metadata_bytes, stream, args.expected_relation_digest)
            elif args.balance_inspection:
                from circuits.transfer_balance_rows import inspect
                with args.balance_inspection.open('rb') as metadata:
                    metadata_bytes = metadata.read(2**20 + 1)
                with args.relation_export.open('rb') as stream:
                    result = inspect(metadata_bytes, stream, args.expected_relation_digest)
            else:
                from circuits.transfer_relation import inspect
                with args.relation_export.open('rb') as stream:
                    result = inspect(stream, expected_relation=args.expected_relation_digest)
            print(json.dumps(result, indent=2))
            return 0
        if args.scope == 'transfer-slice':
            if args.command != 'circuits' or args.model_only:
                raise CheckError('--scope transfer-slice applies only to circuits')
            if args.verify_link:
                if (not args.publication_observation or not args.expected_published_receipt_sha256
                        or args.qualified_receipts or args.candidate_dir):
                    raise CheckError('post-link validation requires observation and independently retained receipt SHA only')
                result = verify_transfer_slice_link(args.source, args.publication_observation, args.expected_published_receipt_sha256)
            else:
                if (not args.qualified_receipts or not args.candidate_dir or args.publication_observation
                        or args.expected_published_receipt_sha256):
                    raise CheckError('slice requires explicit qualified receipts and a fresh candidate directory')
                result = prepare_transfer_slice(args.source, args.qualified_receipts, args.candidate_dir)
                write_result(ROOT / '.work/results/transfer-slice.json', result)
            print(json.dumps(result, indent=2))
            return 0
        if (args.qualified_receipts or args.candidate_dir or args.verify_link
                or args.publication_observation or args.expected_published_receipt_sha256):
            raise CheckError('slice arguments require --scope transfer-slice')
        if args.command == "check":
            print(run([sys.executable, str(ROOT / "reference/inventory.py")], timeout=30))
            print("Current-suite policy valid. Full-system certification: NOT ESTABLISHED.")
            return 0
        if args.command == "release":
            raise CheckError("release blocked: pilot work does not close the seven circuit families and system obligations")
        result = execute_pilot(args.command, args.source, args.model_only)
        write_result(ROOT / ".work/results" / f"{result['pilot']}.json", result)
        print(json.dumps(result, indent=2))
        return 0
    except (CheckError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"security: {error}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    raise SystemExit(main())
