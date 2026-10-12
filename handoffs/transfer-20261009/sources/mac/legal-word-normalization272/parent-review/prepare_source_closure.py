"""Prepare an exact published source closure; never invoke a verifier."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


def read_pin(pin):
    path = Path(pin['path'])
    data = path.read_bytes()
    if len(data) != pin['bytes'] or hashlib.sha256(data).hexdigest() != pin['sha256']:
        raise ValueError(str(path))
    return data


def imports(source):
    # Parse only the import header; body strings and comments cannot add imports.
    pos = 0
    result = []

    def skip():
        nonlocal pos
        while pos < len(source):
            if source[pos].isspace():
                pos += 1
            elif source.startswith('--', pos):
                end = source.find('\n', pos)
                pos = len(source) if end < 0 else end + 1
            elif source.startswith('/-', pos):
                depth = 1
                pos += 2
                while depth:
                    if pos >= len(source):
                        raise ValueError('unterminated header comment')
                    if source.startswith('/-', pos):
                        depth += 1
                        pos += 2
                    elif source.startswith('-/', pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
            else:
                break

    def word():
        nonlocal pos
        skip()
        match = re.match(r'[A-Za-z_][A-Za-z0-9_.]*', source[pos:])
        if not match:
            return None
        pos += match.end()
        return match.group()

    while True:
        token = word()
        if token in {'prelude', 'module'}:
            continue
        if token in {'public', 'private', 'meta'}:
            token = word()
        if token != 'import':
            break
        name = word()
        if name is None:
            raise ValueError('missing import module')
        result.append(name)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--endpoint', required=True)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    config_data = args.config.read_bytes()
    config = json.loads(config_data)
    closure = json.loads(read_pin(config['closure']))
    records = {**closure['modules'], **config['qualified_batch_imports'], **config['modules']}
    needed = {}
    external = set()
    visiting = set()
    order = []

    def visit(name):
        if name in needed:
            return
        if name in visiting:
            raise ValueError('import cycle: ' + name)
        visiting.add(name)
        pin = records[name]['source']
        data = read_pin(pin)
        deps = imports(data.decode())
        for dep in deps:
            if dep.startswith('ShielddSecurity.'):
                visit(dep.removeprefix('ShielddSecurity.'))
            else:
                external.add(dep)
        needed[name] = {'bytes': pin['bytes'], 'sha256': pin['sha256'], 'imports': deps}
        order.append('ShielddSecurity.' + name)
        visiting.remove(name)

    visit(args.endpoint)
    paths = subprocess.check_output(['rg', '--files', '--glob', '*.lean'], cwd=args.repository, text=True).splitlines()
    index = {}
    for relative in paths:
        name = Path(relative).stem
        if name in needed:
            index.setdefault(name, []).append(relative)
    missing = []
    for name, pin in needed.items():
        matches = []
        for relative in index.get(name, []):
            path = args.repository / relative
            if path.stat().st_size != pin['bytes']:
                continue
            if hashlib.sha256(path.read_bytes()).hexdigest() == pin['sha256']:
                matches.append(relative)
        if not matches:
            missing.append(name)
        pin['published_paths'] = sorted(matches)
    if missing:
        raise ValueError('unpublished source identities: ' + ', '.join(missing))
    package_files = {}
    for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
        path = args.repository / 'circuits' / name
        data = path.read_bytes()
        package_files[name] = {'path': 'circuits/' + name, 'bytes': len(data),
                               'sha256': hashlib.sha256(data).hexdigest()}
    result = {
        'kind': 'published exact source/import closure preparation, no kernel replay',
        'endpoint': 'ShielddSecurity.' + args.endpoint,
        'canonical_sha': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=args.repository, text=True).strip(),
        'runtime_sha': config['runtime_sha'],
        'lean_toolchain': 'leanprover/lean4:v4.30.0',
        'mathlib_sha': 'c5ea00351c28e24afc9f0f84379aa41082b1188f',
        'config_sha256': hashlib.sha256(config_data).hexdigest(),
        'custom_sources': needed, 'topological_order': order, 'package_files': package_files,
        'external_imports': sorted(external),
        'portable_generator_closure': 'OPEN', 'final_scoped_replay': 'UNRUN',
        'full_transfer': 'OPEN', 'raw_logs_objects_caches_included': False,
    }
    with args.output.open('x') as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write('\n')
    print(json.dumps({'modules': len(needed), 'bytes': sum(p['bytes'] for p in needed.values()),
                      'external_imports': sorted(external), 'missing': missing}))


if __name__ == '__main__':
    main()
