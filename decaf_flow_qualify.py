#!/usr/bin/env python3
"""Compare candidate BINSEC demand decoding with the original on both ISAs."""
import argparse
import json
import os
from pathlib import Path
import re

import decaf
import formal
from decaf_inventory import atomic_json
from security import bounded_run

def require(condition, detail):
    if not condition:
        raise ValueError(str(detail))


def main():
    root = formal.ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dune-root', required=True, type=Path)
    args = parser.parse_args()
    work = root / '.work/decaf-flow-qualification'
    work.mkdir(exist_ok=True)
    report_path = work / 'report.json'
    env = dict(os.environ, OPAMROOTISOK='1', OCAMLPATH='', GIT_NO_REPLACE_OBJECTS='1')
    base = ['opam', 'exec', '--switch=binsec-fv', '--']
    report = {'status': 'blocked', 'completed': False, 'full_certification': False, 'qualification_complete': False,
              'scope': 'differential supported flow and reached/unreached unsupported-instruction controls',
              'commands': [], 'cases': [], 'experiment_sha256': formal.file_digest(Path(__file__)),
              'source_sha256': formal.file_digest(root / 'decaf/proofs/binary/flow-controls.c'),
              'classifier_sha256': formal.file_digest(root / 'decaf.py'),
              'patch_sha256': formal.file_digest(root / 'decaf/proofs/binsec-demand-decoding.patch')}
    
    def command(argv, timeout=60):
        argv = list(map(str, argv))
        log = work / ('%03d.log' % len(report['commands']))
        report['commands'].append({'argv': argv, 'log': str(log)})
        bounded_run(argv, work, env, log, work / 'unused', work, timeout)
        return log.read_text()
    
    with formal.exclusive_lock():
        atomic_json(report_path, report)
        try:
            source_root = args.dune_root.resolve(strict=True)
            prefixes = {'original': base, 'demand': base + ['dune', 'exec', '--profile', 'release', '--root', source_root, '--']}
            revision = json.loads((root / 'decaf/inputs.json').read_text())['binsec']['revision']
            git = ['git', '-C', source_root]
            require(command(git + ['rev-parse', 'HEAD']).strip() == revision, 'candidate source revision changed')
            name = 'src/sse/exec.ml'
            original = command(git + ['show', 'HEAD:' + name])
            old = 'let fiber = Disassembly.disassemble_from code addr in'
            new = 'let fiber = Disassembly.fetch_no_link code addr in'
            require(original.count(old) == 1 and (source_root / name).read_text() == original.replace(old, new)
                    and command(git + ['diff', '--name-only', 'HEAD']).splitlines() == [name],
                    'candidate source differs from single-site demand decoding patch')
            report['candidate_source'] = dict(revision=revision, modified_source_sha256=formal.file_digest(source_root / name))
            report['process_runner_sha256'] = formal.file_digest(root / 'security.py')
            report['tools'] = {}
            installation = Path(command(['opam', 'var', '--switch=binsec-fv', 'prefix']).strip())
            for name, prefix in prefixes.items():
                tool = Path(command(prefix + ['which', 'binsec']).strip()).resolve(strict=True)
                solver = Path(command(prefix + ['which', 'z3']).strip()).resolve(strict=True)
                report['tools'][name] = {'path': str(tool), 'sha256': formal.file_digest(tool),
                    'version': command(prefix + [tool, '-version']).strip(),
                    'solver': {'path': str(solver), 'sha256': formal.file_digest(solver),
                               'version': command(prefix + [solver, '--version']).strip()},
                    'components': {str(path): formal.file_digest(path)
                        for package in ('binsec', 'unisim_archisec')
                        for component_root in ([source_root / '_build/install/default']
                                               if name == 'demand' and package == 'binsec' else [installation])
                        for path in sorted((component_root / 'lib' / package).rglob('*'))
                        if path.is_file() and path.suffix in {'.cmxs', '.so'}}}
            report['component_note'] = 'installed/build component identities; actual dynamic loading is not attested'
            report['build_tools'] = {}
            for target, compiler in [('x86_64', 'gcc'), ('aarch64', 'aarch64-linux-gnu-gcc')]:
                compiler = Path(command(['which', compiler]).strip()).resolve(strict=True)
                nm = Path(command(['which', 'nm']).strip()).resolve(strict=True)
                report['build_tools'][target] = {
                    'compiler': {'path': str(compiler), 'sha256': formal.file_digest(compiler),
                                 'version': command([compiler, '--version']).strip()},
                    'nm': {'path': str(nm), 'sha256': formal.file_digest(nm)}}
                for control in [0, 1, 2, 3, 4, 5]:
                    binary = work / f'{target}-{control}'
                    binary.unlink(missing_ok=True)
                    command([compiler, '-O0', '-g', '-fno-pie', '-no-pie', f'-DCONTROL={control}',
                             root / 'decaf/proofs/binary/flow-controls.c', '-o', binary])
                    symbols = command([nm, '-n', binary])
                    def address(name):
                        matches = re.findall(r'^([0-9a-f]+) [A-Za-z] ' + name + r'$', symbols, re.M)
                        require(len(matches) == 1, 'missing or ambiguous symbol: ' + name)
                        return int(matches[0], 16)
                    endpoint, gate = address('decaf_done'), address('decaf_gate')
                    variants = ['public']
                    if control == 0:
                        variants += ['depth']
                    if control == 3:
                        variants = ['zero', 'one', 'public']
                    if control == 4:
                        variants = ['timeout']
                    for variant in variants:
                        cfg = work / f'{target}-{control}-{variant}.cfg'
                        config = ('starting from <decaf_entry>\nwith concrete stack pointer\n'
                                  'secret global decaf_secret\npublic global decaf_gate\npublic global decaf_memory\n')
                        if variant in ('zero', 'one'):
                            config += f'@[0x{gate:x}, 4] := {int(variant == "one")}\n'
                        config += f'reach 0x{endpoint:x}\nhalt at 0x{endpoint:x}\nexplore all\n'
                        decaf.validate_analysis_config(config)
                        cfg.write_text(config)
                        pair = {}
                        for name, prefix in prefixes.items():
                            case = {'id': f'{target}-{control}-{variant}-{name}', 'status': 'blocked',
                                    'binary_sha256': formal.file_digest(binary), 'config_sha256': formal.file_digest(cfg)}
                            report['cases'].append(case)
                            atomic_json(report_path, report)
                            output = command(prefix + [report['tools'][name]['path'], '-sse', '-checkct', '-checkct-leak-info', 'instr',
                                '-smt-solver', 'z3', '-sse-script', cfg, '-sse-depth',
                                '1' if variant == 'depth' else '1000000000',
                                '-sse-timeout', '1' if variant == 'timeout' else '20', binary], 45)
                            expected = 'insecure' if control in (1, 2, 5) else 'secure'
                            raw_status, detail = decaf.classify_analysis(output, expected, endpoint)
                            case.update(analysis_status=raw_status, detail=detail)
                            if variant in ('depth', 'timeout'):
                                require(raw_status == 'blocked' and variant in output.lower(), case)
                            elif control == 3 and variant == 'zero' and name == 'original':
                                require(raw_status == 'passed' or (raw_status == 'blocked' and re.search(r':error\]|uninterpreted|unsupported', output, re.I)), case)
                            elif control == 3 and variant != 'zero':
                                require(raw_status == 'blocked' and re.search(r':error\]|uninterpreted|unsupported', output, re.I), case)
                            else:
                                require(raw_status == 'passed', case)
                                if control in (1, 5):
                                    require('control flow leak' in output, 'missing branch leak')
                                if control == 2:
                                    require('memory access leak' in output, 'missing address leak')
                            case['leaks'] = sorted(set(re.findall(r'Instruction (0x[0-9a-f]+) has (control flow|memory access) leak', output)))
                            case['endpoints'] = sorted(set(re.findall(r'Path \d+ reached address (0x[0-9a-f]+)', output)))
                            case['completed_paths'] = re.findall(r'completed/cut paths\s+(\d+)', output)
                            case['status'] = 'passed'
                            pair[name] = case
                            atomic_json(report_path, report)
                        if control in (0, 1, 2, 5) and variant == 'public':
                            require(all(len(case['completed_paths']) == 1 for case in pair.values()),
                                    'missing or ambiguous completed-path statistics')
                            for key in ('leaks', 'endpoints', 'completed_paths'):
                                require(pair['original'][key] == pair['demand'][key], (target, control, key, pair))
            require(len(report['cases']) == 36 and all(case['status'] == 'passed' for case in report['cases']),
                    'incomplete differential control matrix')
            report.update(status='passed', completed=True)
        except (Exception, KeyboardInterrupt) as error:
            report['detail'] = str(error) or 'interrupted'
        finally:
            atomic_json(report_path, report)
        print(json.dumps({'status': report['status'], 'report': str(report_path)}))
        return 0 if report['status'] == 'passed' else 1
    

if __name__ == '__main__':
    raise SystemExit(main())
