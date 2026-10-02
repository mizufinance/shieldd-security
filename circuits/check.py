"""Exact compiler exports, kernel certificates and semantic controls (Linux)."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from security import (ROOT, CheckError, run, locked_sha, check_register,
                      runtime_identity, source_identity, transfer_slice_proof_inputs,
                      TRANSFER_SLICE_SHA, TRANSFER_SLICE_THEOREMS,
                      read_json_bytes, verified_bytes)
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_locks(source):
    runtime = tomllib.loads((source / 'Cargo.lock').read_text())
    harness = tomllib.loads((ROOT / 'integration/Cargo.lock').read_text())
    identity = lambda p: (p['name'], p['version'], p.get('source'), p.get('checksum'))
    allowed = {identity(p) for p in runtime['package']}
    extra = [identity(p) for p in harness['package'] if p.get('source') and identity(p) not in allowed]
    if extra:
        raise CheckError(f'integration dependencies differ from runtime lock: {extra}')
    packages = json.loads((ROOT / 'circuits/lake-manifest.json').read_text())['packages']
    for package in packages:
        checkout = ROOT / 'circuits/.lake/packages' / package['name']
        if run(['git', 'rev-parse', 'HEAD'], checkout) != package['rev']:
            raise CheckError(f'Lean dependency revision mismatch: {package["name"]}')
        if run(['git', 'status', '--porcelain', '--untracked-files=no'], checkout):
            raise CheckError(f'dirty Lean dependency: {package["name"]}')
    return packages


def lean_environment(packages, root=ROOT):
    executable = shutil.which('lean')
    if executable is None:
        raise CheckError('Lean 4.30.0 is missing from PATH')
    executable = str(Path(executable).resolve())
    version = run([executable, '--version'])
    token = re.search(r'\bversion ([^,\s)]+)', version)
    if token is None or token.group(1) != '4.30.0':
        raise CheckError(f'wrong Lean toolchain: {version}')
    paths, modules = [], set()
    for package in packages:
        path = root / 'circuits/.lake/packages' / package['name'] / '.lake/build/lib/lean'
        if not path.is_dir():
            continue  # A narrow cache need not build unused dependencies.
        paths.append(str(path))
        for artifact in path.rglob('*.olean'):
            module = artifact.relative_to(path).with_suffix('').as_posix()
            if module in modules or module == 'ShielddSecurity' or module.startswith('ShielddSecurity/'):
                raise CheckError(f'conflicting cached Lean module: {module}')
            modules.add(module)
    for module in ['Mathlib/Algebra/Field/Basic', 'Mathlib/Tactic/Ring/RingNF', 'Mathlib/Algebra/CharP/Defs']:
        if module not in modules:
            raise CheckError(f'missing pinned Lean cache module: {module}')
    return {'lean': executable, 'version': version, 'path': os.pathsep.join(paths)}


def prepare_transfer_slice(source, qualification, candidate_dir):
    """Validate previously qualified narrow results; launches no proof job."""
    from circuits.statement_projection import generate
    source = Path(source).resolve()
    sha = locked_sha()
    if sha != TRANSFER_SLICE_SHA:
        raise CheckError('transfer-slice supports only the exact PR160 lock')
    register_bytes = verified_bytes(ROOT / 'assurance.json')
    register_sha256 = hashlib.sha256(register_bytes).hexdigest()
    register = check_register()
    if register != read_json_bytes(register_bytes):
        raise CheckError('register changed before preregistered qualification read')
    if register['claims']['system']['status'] != 'blocked':
        raise CheckError('a development slice cannot promote system certification')
    try:
        entry = register['claims']['system']['development_evidence']['reduced_transfer_slice']
        authority = entry['qualification']
    except (KeyError, TypeError) as error:
        raise CheckError('substantive slice inputs must be predeclared before validation') from error
    if (entry.get('schema') != 'reduced-transfer-slice-inputs-v1' or entry.get('runtime_sha') != sha
            or entry.get('status') != 'blocked' or entry.get('policy') != 'development_only'
            or entry.get('theorems') != TRANSFER_SLICE_THEOREMS
            or not entry.get('scope') or not entry.get('limits') or not entry.get('assumptions')):
        raise CheckError('incomplete or enlarged transfer-slice preregistration')
    qualification = Path(qualification).resolve()
    def raw(path):
        return hashlib.sha256(verified_bytes(path)).hexdigest()
    if qualification != (ROOT / authority['path']).resolve():
        raise CheckError('qualification path differs from preregistered acceptance')
    # Never replace this expected pin with a newly observed digest.
    qualification_sha256 = authority['sha256']
    review = read_json_bytes(verified_bytes(qualification, qualification_sha256))
    checked_refs = {str(qualification): qualification_sha256}
    # This explicit, preregistered acceptance is a human-review authority TCB.
    # A caller-provided result.success flag is never an acceptance mechanism.
    roles = {'comparison', 'decision', 'projection', 'permanent_spend', 'controls', 'source_joins'}
    if (review.get('schema') != 'qualified-reduced-transfer-artifacts-v1'
            or review.get('runtime_sha') != sha or review.get('scope') != 'transfer-slice'
            or review.get('acceptance') != 'independently_qualified_actual_results'
            or set(review.get('artifacts', {})) != roles):
        raise CheckError('missing exact independent qualification coverage')
    before = {'runtime': runtime_identity(source, sha), 'raw_source': source_identity(),
              'raw_register_sha256': hashlib.sha256(verified_bytes(ROOT / 'assurance.json', register_sha256)).hexdigest(),
              'proof_inputs': transfer_slice_proof_inputs()}
    artifacts, artifact_refs = {}, {}
    for role in sorted(roles):
        ref = review['artifacts'][role]
        path = (ROOT / ref['path']).resolve()
        data = verified_bytes(path, ref['sha256'])
        artifact_refs[role] = {'path': str(path), 'sha256': ref['sha256']}
        checked_refs[str(path)] = ref['sha256']
        artifacts[role] = read_json_bytes(data)
        if artifacts[role].get('runtime_sha') != sha:
            raise CheckError(f'qualified {role} belongs to another runtime')
    decision = artifacts['decision']
    if (decision.get('basis_comparison_sha256') != artifact_refs['comparison']['sha256']
            or decision.get('chosen_approach') not in {'clean', 'direct-lean'}
            or decision.get('scope') != 'matched permanent-spend four-gate comparison'):
        raise CheckError('actual comparable spike and documented approach decision are required')
    if artifacts['comparison'].get('matched_property') != 'permanent-spend-four-gates-v1':
        raise CheckError('comparison covers a different property')
    joins = artifacts['source_joins']
    required_proofs = {'circuits/statement_projection.py', 'circuits/ShielddSecurity/TransferStatement.lean',
                       'circuits/ShielddSecurity/PermanentSpend.lean',
                       'circuits/ShielddSecurity/Rows.lean', 'circuits/ShielddSecurity/Range.lean',
                       'circuits/ShielddSecurity/SpendGateInputs.lean'}
    if set(joins.get('proof_sources', {})) != required_proofs or not joins.get('assumptions'):
        raise CheckError('exact proof sources and source-reading assumptions required')
    for relative, digest in joins['proof_sources'].items():
        verified_bytes(ROOT / relative, digest)
        checked_refs[str((ROOT / relative).resolve())] = digest
    required_runtime = {'lib.rs', 'transfer.rs', 'encryption.rs', 'audit.rs', 'group.rs', 'note.rs'}
    if set(joins.get('runtime_sources', {})) != required_runtime:
        raise CheckError('five AST sources and permanent note source required')
    for name, digest in joins['runtime_sources'].items():
        runtime_path = source / 'crates/crypto/circuits/src' / name
        verified_bytes(runtime_path, digest)
        checked_refs[str(runtime_path)] = digest
    for role in ('projection', 'permanent_spend'):
        evidence = artifacts[role]
        if (set(evidence.get('theorems', {})) != set(TRANSFER_SLICE_THEOREMS[role])
                or evidence.get('scope') != role):
            raise CheckError(f'exact named {role} theorem coverage required')
        for name, audit in evidence['theorems'].items():
            if not audit.get('full_statement') or not audit.get('premises') or not audit.get('conclusion'):
                raise CheckError(f'missing full theorem interface: {name}')
            path = (ROOT / audit['log']['path']).resolve()
            text = verified_bytes(path, audit['log']['sha256']).decode('utf-8')
            reports = re.findall(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", text, re.S)
            none = re.findall(r"'" + re.escape(name) + r"' does not depend on any axioms", text)
            if len(reports) + len(none) != 1 or audit['full_statement'] not in text or 'sorryAx' in text:
                raise CheckError(f'missing full named audit: {name}')
            if reports and any(not re.fullmatch(r'(?:propext|Classical\.choice|Quot\.sound)(?:\.\{(?:[A-Za-z_][A-Za-z0-9_]*|0)\})?', value.strip())
                               for value in reports[0].split(',') if value.strip()):
                raise CheckError(f'nonstandard axiom: {name}')
            checked_refs[str(path)] = audit['log']['sha256']
    controls = artifacts['controls']
    expected = {'boolean': [2,0,2,0,1,0,0], 'selection': [0,0,1,0,0,0,0],
                'root': [0,0,0,0,0,1,0], 'amount': [1,1,0,0,0,0,0]}
    if (controls.get('canonical_source_sha256') != joins['proof_sources']['circuits/ShielddSecurity/PermanentSpend.lean']
            or set(controls.get('omissions', {})) != set(expected)
            or len(controls.get('AST_rejections', [])) != 6
            or controls.get('adapter_coordinate_rejections') != ['helper coordinate order']
            or len(controls.get('map_rejections', [])) != 4):
        raise CheckError('canonical semantic and structural control joins missing')
    for name, witness in expected.items():
        observed = controls['omissions'][name]
        if (observed.get('field_modulus') != 17 or observed.get('assignment_d_a_n_r_s_c_h') != witness
                or observed.get('retained_gates') != [True,True,True]
                or observed.get('omitted_gate') is not False or observed.get('independent_BranchSpec') is not False):
            raise CheckError(f'intended semantic omission not observed: {name}')
    # Every exact audit/control/source/compiled-provider reference approved by the
    # pinned independent review is mandatory, current, and checked again below.
    if not review.get('raw_refs'):
        raise CheckError('qualified actual execution, imports, cleanup and control raw references required')
    for ref in review['raw_refs']:
        path = (ROOT / ref['path']).resolve()
        verified_bytes(path, ref['sha256'])
        if str(path) in checked_refs and checked_refs[str(path)] != ref['sha256']:
            raise CheckError(f'conflicting qualified raw reference: {path}')
        checked_refs[str(path)] = ref['sha256']
    projection = artifacts['projection']
    export_path = (ROOT / projection['AST_export']['path']).resolve()
    export_bytes = verified_bytes(export_path, projection['AST_export']['sha256'])
    export = read_json_bytes(export_bytes)
    audited = (ROOT / projection['audited_generated_source']['path']).resolve()
    audited_bytes = verified_bytes(audited, projection['audited_generated_source']['sha256'])
    checked_refs[str(export_path)] = projection['AST_export']['sha256']
    checked_refs[str(audited)] = projection['audited_generated_source']['sha256']
    candidate_dir = Path(candidate_dir).resolve()
    if not candidate_dir.is_relative_to((ROOT / '.work').resolve()) or candidate_dir.exists():
        raise CheckError('fresh immutable candidate directory under .work required')
    candidate_dir.mkdir(parents=True)
    generated = candidate_dir / 'RuntimeTransferStatement.lean'
    with generated.open('xb') as handle:
        handle.write(generate(export).encode('utf-8'))
        handle.flush(); os.fsync(handle.fileno())
    generated_bytes = verified_bytes(generated)
    if generated_bytes != audited_bytes:
        raise CheckError('generated 64-role candidate differs from actually audited source')
    generated_sha256 = hashlib.sha256(generated_bytes).hexdigest()
    checked_refs[str(generated)] = generated_sha256
    for ref in artifact_refs.values():
        checked_refs[ref['path']] = ref['sha256']
    for path, digest in checked_refs.items():
        verified_bytes(path, digest)
    after = {'runtime': runtime_identity(source, sha), 'raw_source': source_identity(),
             'raw_register_sha256': hashlib.sha256(verified_bytes(ROOT / 'assurance.json', register_sha256)).hexdigest(),
             'proof_inputs': transfer_slice_proof_inputs()}
    if after != before:
        raise CheckError('slice inputs changed; no result promotion')
    return {'pilot': 'transfer-slice', 'outcome': 'qualified_development_artifacts_unlinked',
            'runtime': before['runtime'], 'proof_inputs': before['proof_inputs'],
            'raw_pre': before, 'raw_post': after, 'artifacts': artifact_refs,
            'checked_raw_refs': checked_refs, 'approach': decision['chosen_approach'],
            'generated_mapping': {'path': str(generated), 'sha256': generated_sha256},
            'theorems': TRANSFER_SLICE_THEOREMS, 'assumptions': entry['assumptions'],
            'limits': entry['limits'], 'full_system_certification': 'not_established',
            'register_linkage': 'requires_separate_post_link_validation'}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--scope', choices=['legacy', 'transfer-slice'], default='legacy')
    parser.add_argument('--qualified-receipts', type=Path)
    parser.add_argument('--candidate-dir', type=Path)
    args = parser.parse_args()
    if args.scope == 'transfer-slice':
        if not args.qualified_receipts or not args.candidate_dir:
            raise CheckError('narrow slice requires explicit qualified receipts and fresh candidate')
        print(json.dumps(prepare_transfer_slice(args.source, args.qualified_receipts, args.candidate_dir)))
        return
    if args.qualified_receipts or args.candidate_dir:
        raise CheckError('qualified slice inputs require --scope transfer-slice')
    from generate import generate as range_generate
    from generate_volume import generate as volume_generate
    from controls import controls as range_controls
    from compiler_controls import check as compiler_controls
    from volume_controls import check as volume_controls
    if os.name == 'nt':
        raise CheckError('run the entire circuit CLI inside Linux/WSL')
    source = args.source.resolve()
    if source != (ROOT / '.work/shieldd-current').resolve():
        raise CheckError('integration requires the checked .work/shieldd-current source')
    packages = check_locks(source)
    provenance_check = run([sys.executable, str(source / 'scripts/commonware.py'), 'check'], cwd=source, timeout=120)
    output = ROOT / '.work/circuits'
    output.mkdir(parents=True, exist_ok=True)
    cargo = ['env', 'CARGO_BUILD_JOBS=1', 'RAYON_NUM_THREADS=1', 'CARGO_ENCODED_RUSTFLAGS=',
             f'CARGO_TARGET_DIR={os.environ.get("CARGO_TARGET_DIR", ROOT / ".cache/cargo-target")}',
             'cargo', '+1.95.0', 'run', '--locked', '--profile', 'ci', '--manifest-path', str(ROOT / 'integration/Cargo.toml')]
    # The helper compiles a disposable exact-base archive and never edits the
    # selected runtime. Its dependency identities and build options match.
    baseline = json.loads(run([sys.executable, str(ROOT / 'circuits/baseline.py')], timeout=960))
    artifacts = {}
    for binary in ['circuit-export', 'volume-export', 'compiler-controls']:
        raw = run(cargo + ['--bin', binary], timeout=600)
        path = output / f'{binary}.json'
        path.write_text(raw + '\n')
        artifacts[binary] = json.loads(raw)
    volume = artifacts['volume-export']
    for key in ['relation_digest', 'domain_size', 'public_inputs', 'committed_blocks', 'layout']:
        if baseline[key] != volume[key]:
            raise CheckError(f'observation changed original Transfer {key}')
    controls = {'range': range_controls(artifacts['circuit-export']),
                'compiler': compiler_controls(artifacts['compiler-controls']),
                'volume': volume_controls(volume)}
    environment = lean_environment(packages)
    version = environment['version']
    logs = {}
    expected_audits = {
        'Range': ['boolean_sound', 'range_sound', 'range_completeness', 'outlined_one', 'deferred_square', 'product_encoding'],
        'Rows': ['rows_range_sound', 'range_rows_complete'],
        'Arithmetic': ['addition_lift', 'comparison_lift'],
        'Volume': ['volume_arithmetic_sound'],
        'RuntimeRange': ['range128_sound', 'public_range128_sound', 'emitted_range_completeness', 'input_completeness'],
        'RuntimeVolume': ['volume_sound', 'volume_input_completeness'],
    }
    # A fresh output directory prevents stale local olean files from replacing
    # the handwritten sources or newly generated literal-row certificates.
    with tempfile.TemporaryDirectory(dir=output, prefix='kernel-') as staging:
        stage = Path(staging)
        package = stage / 'ShielddSecurity'
        package.mkdir()
        for name, text in [('RuntimeRange', range_generate(artifacts['circuit-export'])),
                           ('RuntimeVolume', volume_generate(volume))]:
            (package / f'{name}.lean').write_text(text)
        for module in ['Range', 'Rows', 'Arithmetic', 'Volume', 'RuntimeRange', 'RuntimeVolume']:
            generated = module.startswith('Runtime')
            source_root = stage if generated else ROOT / 'circuits'
            source_file = source_root / 'ShielddSecurity' / f'{module}.lean'
            if re.search(r'\b(sorry|admit|axiom)\b', source_file.read_text()):
                raise CheckError(f'prohibited proof escape in {source_file}')
            command = ['env', 'LEAN_NUM_THREADS=1', f'LEAN_PATH={stage}:{environment["path"]}',
                       environment['lean'], '--root', str(source_root), '-o', str(package / f'{module}.olean'), str(source_file)]
            logs[module] = run(command, timeout=300)
            for theorem in expected_audits[module]:
                if not re.search(rf"['\w.]*\.{theorem}'? (?:depends on axioms:|does not depend on any axioms)", logs[module]):
                    raise CheckError(f'missing axiom audit for {module}.{theorem}')
            if 'sorryAx' in logs[module]:
                raise CheckError(f'unsound axiom in {module}')
            for axioms in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', logs[module]):
                if set(re.findall(r'[\w.]+', axioms)) - {'propext', 'Classical.choice', 'Quot.sound'}:
                    raise CheckError(f'unexpected axioms in {module}: {axioms}')
            (output / f'{module}.log').write_text(logs[module])
        for name in ['RuntimeRange', 'RuntimeVolume']:
            # Generated evidence is promoted only after both certificates pass.
            os.replace(package / f'{name}.lean', output / f'{name}.lean')
    result = {'outcome': 'passed', 'scope': 'isolated public range and precise actual Transfer arithmetic slice',
              'limits': ['exporter, canonical coefficient translation and row membership are trusted joins',
                         'arithmetic completeness excludes surrounding crypto and whole-family inputs',
                         'compiler controls are finite regressions, not a whole compiler proof'],
              'baseline': baseline, 'controls': controls, 'lean': version,
              'lean_executable': environment['lean'], 'commonware_check': provenance_check,
              'rustc': run(['rustc', '+1.95.0', '--version']),
              'build': {'profile': 'ci', 'rustflags': [], 'jobs': 1, 'features': 'integration/Cargo.toml'},
              'budgets_seconds': {'baseline_total':900, 'export':600, 'named_lean_module':300},
              'inputs': {str(path.relative_to(ROOT)): digest(path) for path in [ROOT / 'integration/Cargo.lock', ROOT / 'integration/Cargo.toml', ROOT / 'circuits/lake-manifest.json', ROOT / 'circuits/lean-toolchain']},
              'artifacts': {path.name: digest(path) for path in output.iterdir() if path.is_file()},
              'relations': {name: data.get('relation_digest') for name, data in artifacts.items()},
              'axiom_audits': logs}
    print(json.dumps(result))


if __name__ == '__main__':
    main()
