"""Transport sealed registry sources and structured receipts without replay."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    for name in ['packet', 'review', 'destination']:
        parser.add_argument('--' + name, required=True, type=Path)
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
    census = json.loads((args.packet / 'execution-census01.json').read_bytes())
    for record in census['receipts']:
        put('receipts/' + Path(record['path']).name, Path(record['path']), record)
    for name in ['producer-manifest01.json', 'envelope01.json', 'postseal-guard01.json',
                 'qualified-modules01.json', 'full-audits01.json', 'scope01.json',
                 'execution-census01.json', 'maintained-source-references01.json']:
        put('provenance/' + name, args.packet / name)
    refs = json.loads((args.packet / 'maintained-source-references01.json').read_bytes())
    for key, directory in [('prefix_generator', 'maintained/prefix'),
                           ('tail_generator', 'maintained/tail'),
                           ('whole_generator', 'maintained/whole'),
                           ('whole_template', 'maintained/whole'),
                           ('actual_result', 'generator-input')]:
        record = refs[key]
        put(directory + '/' + Path(record['path']).name, Path(record['path']), record)
    for name in ['audit_endpoint.py', 'audit-result01.json', 'endpoint-review.md',
                 'result-data-review01.json', 'endpoint-regeneration01.json']:
        put('parent-review/' + name, args.review / name)
    manifest = {'kind': 'exact scoped source and structured receipt transport; no new replay',
                'producer_sha256': '11fc940297fded9685dc40e77e575c7481634469ac6cc027a32474fc7bdd3a27',
                'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
                'files': entries, 'raw_logs_objects_caches_included': False,
                'full_transfer': 'OPEN', 'full_row_kernel_instance': 'OPEN',
                'portable_generation_import_closure': 'OPEN; historical helper recipes remain integration work',
                'certification_refresh': False}
    with (args.destination / 'publication-manifest01.json').open('x') as handle:
        json.dump(manifest, handle, indent=2, sort_keys=True)
        handle.write('\n')
    print(json.dumps({'files': len(entries), 'bytes': sum(v['bytes'] for v in entries.values())}))


if __name__ == '__main__':
    main()
