"""Transport reviewed symbolic source and structured records; no replay."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--review', type=Path, required=True)
    parser.add_argument('--destination', type=Path, required=True)
    args = parser.parse_args()
    original = (args.packet / 'manifest.json').read_bytes()
    if hashlib.sha256(original).hexdigest() != '84794788233ce0810f08ae98c46a9dbe13966567a30ee5549faf2b4ebcedb96d':
        raise ValueError('capsule identity')
    manifest = json.loads(original)
    files, excluded = {}, []

    def put(name, data, provenance):
        path = args.destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as handle:
            handle.write(data)
        files[name] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(), 'original': provenance}

    for entry in manifest['files']:
        name = entry['path']
        data = (args.packet / name).read_bytes()
        if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise ValueError(name)
        if name.startswith('audit-output/'):
            excluded.append(name)
            continue
        if Path(name).suffix not in {'.lean', '.py', '.json'}:
            raise ValueError('unexpected transport role: ' + name)
        put(name, data, entry.get('original', entry.get('source', 'sealed capsule record')))
    put('provenance/original-capsule-manifest.json', original, 'sealed capsule')
    for name in ['audit_endpoint.py', 'audit-result01.json', 'endpoint-review.md']:
        put('parent-review/' + name, (args.review / name).read_bytes(), 'independent parent review')
    publication = {k: v for k, v in manifest.items() if k != 'files'}
    publication.update({'kind': 'reviewed scoped source and structured receipt transport; no new replay',
                        'files': files, 'excluded_local_raw_outputs': excluded,
                        'original_archive_sha256': '893c6ff131e8cbc02d7183ff74b138fcd776ba954f947e4418cbe88609e94a97',
                        'parent_object_import_inventory_replay': False,
                        'portable_executable_recipe_replay': 'OPEN; exact host-specific recipe provenance',
                        'raw_logs_objects_caches_included': False})
    with (args.destination / 'publication-manifest01.json').open('x') as handle:
        json.dump(publication, handle, indent=2, sort_keys=True)
        handle.write('\n')
    print(json.dumps({'files': len(files), 'bytes': sum(f['bytes'] for f in files.values()), 'excluded_raw_outputs': len(excluded)}))


if __name__ == '__main__':
    main()
