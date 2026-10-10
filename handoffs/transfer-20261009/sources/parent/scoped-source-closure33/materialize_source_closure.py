"""Copy an exact scoped source closure from publication; no build or cache use."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--destination', required=True, type=Path)
    args = parser.parse_args()
    manifest_data = args.manifest.read_bytes()
    manifest = json.loads(manifest_data)
    repo = args.repository.resolve()
    dest = args.destination.resolve()
    if dest == repo or repo in dest.parents:
        raise ValueError('composed source workspace must be outside publication')
    dest.mkdir(exist_ok=False)

    def copy(relative, pin, candidates):
        for candidate in candidates:
            source = (repo / candidate).resolve()
            if repo not in source.parents:
                raise ValueError('source outside repository')
            data = source.read_bytes()
            if len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']:
                target = dest / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open('xb') as handle:
                    handle.write(data)
                return
        raise ValueError('no exact source: ' + relative)

    for name, pin in manifest['custom_sources'].items():
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name):
            raise ValueError('unsupported module name')
        copy('ShielddSecurity/' + name + '.lean', pin, pin['published_paths'])
    for name, pin in manifest['package_files'].items():
        if name not in {'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'}:
            raise ValueError('unsupported package file')
        copy(name, pin, [pin['path']])
    receipt = {'kind': 'exact source materialization only, no build or cache import',
               'manifest_sha256': hashlib.sha256(manifest_data).hexdigest(),
               'endpoint': manifest['endpoint'], 'sources': len(manifest['custom_sources']),
               'package_files': len(manifest['package_files']), 'destination': str(dest),
               'final_scoped_replay': 'UNRUN', 'full_transfer': 'OPEN'}
    with (dest / 'source-materialization01.json').open('x') as handle:
        json.dump(receipt, handle, indent=2)
        handle.write('\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
