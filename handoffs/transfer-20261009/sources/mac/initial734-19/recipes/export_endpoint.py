"""Transport exact accepted endpoint sources and summaries, without replay."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', required=True, type=Path)
    parser.add_argument('--review', required=True, type=Path)
    parser.add_argument('--destination', required=True, type=Path)
    args = parser.parse_args()
    entries = {}

    def put(relative, path, pin=None):
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if pin and (digest != pin['sha256'] or len(data) != pin['bytes']):
            raise ValueError(str(path))
        dest = args.destination / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        with dest.open('xb') as handle:
            handle.write(data)
        entries[relative] = {'bytes': len(data), 'sha256': digest, 'original': str(path)}

    modules = json.loads((args.packet / 'qualified-modules01.json').read_bytes())
    for name, record in modules.items():
        put('sources/ShielddSecurity/' + name + '.lean', Path(record['source']['path']), record['source'])
        put('receipts/' + name + '.json', Path(record['receipt']['path']), record['receipt'])
    for name in ['producer-manifest01.json', 'envelope01.json', 'postseal-guard01.json',
                 'qualified-modules01.json', 'full-audits01.json', 'scope01.json',
                 'execution-census01.json', 'source-generation-references01.json']:
        put('provenance/' + name, args.packet / name)
    refs = json.loads((args.packet / 'source-generation-references01.json').read_bytes())
    for key in ['current_endpoint_generator', 'endpoint_renderer']:
        record = refs[key]
        put('maintained/' + Path(record['path']).name, Path(record['path']), record)
    record = refs['frozen_data']
    put('generator-input/' + Path(record['path']).name, Path(record['path']), record)
    for name in ['audit_endpoint.py', 'audit-result01.json', 'endpoint-review.md',
                 'row-data-review01.json', 'endpoint-regeneration01.json']:
        put('parent-review/' + name, args.review / name)
    manifest = {'kind': 'exact scoped source and structured receipt transport; no new replay',
                'producer_sha256': '6dacc738db79ac23f7209e669a3dbefb02139202ffa2845a83a3aaf620e92124',
                'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
                'files': entries, 'raw_logs_objects_caches_included': False,
                'full_transfer': 'OPEN', 'full_row_kernel_instance': 'OPEN',
                'portable_generation_import_closure': 'OPEN; latest endpoint generator is not a byte recipe for all historical helpers',
                'certification_refresh': False}
    with (args.destination / 'publication-manifest01.json').open('x') as handle:
        json.dump(manifest, handle, indent=2, sort_keys=True)
        handle.write('\n')
    print(json.dumps({'files': len(entries), 'bytes': sum(v['bytes'] for v in entries.values())}))


if __name__ == '__main__':
    main()
