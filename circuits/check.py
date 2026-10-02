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
from security import ROOT, CheckError, run
from generate import generate as range_generate
from generate_volume import generate as volume_generate
from controls import controls as range_controls
from compiler_controls import check as compiler_controls
from volume_controls import check as volume_controls


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, required=True)
    args = parser.parse_args()
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
