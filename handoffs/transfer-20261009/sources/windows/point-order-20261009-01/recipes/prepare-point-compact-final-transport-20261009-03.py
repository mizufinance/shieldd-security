from pathlib import Path
import argparse, base64, hashlib, json, lzma

p = argparse.ArgumentParser()
p.add_argument('--packet', required=True, choices=['point-trace-complete', 'point-order'])
args = p.parse_args()
local = Path('C:/src/shieldd-transfer-handoffs')
repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
source = local / (args.packet + '-review-packet-20261009-02')
dest = local / (args.packet + '-compact-review-packet-20261009-03')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
original = load(source / 'manifest.json')
assert not dest.exists()
dest.mkdir()
files, references = {}, {}
trace = local / 'point-trace-complete-review-packet-20261009-02'

def copy(path, rel):
    out = dest / rel
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(path.read_bytes())
    files[rel] = {'sha256': sha(out), 'bytes': out.stat().st_size}

def write(rel, value):
    out = dest / rel
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes((json.dumps(value, indent=2) + '\n').encode())
    files[rel] = {'sha256': sha(out), 'bytes': out.stat().st_size}

for rel, identity in original['files'].items():
    path = source / rel
    assert sha(path) == identity['sha256'] and path.stat().st_size == identity['bytes']
    if rel.startswith('resource-samples/') and rel.endswith('.txt'):
        rows = [line.split() for line in path.read_text(encoding='utf-8-sig').splitlines() if line.strip()]
        if 'scoped-artifact-disk' in rel:
            sizes = [int(float(row[-1])) for row in rows]
            assert sizes and max(sizes) <= 2147483648
            summary = {'samples': len(rows), 'peak_staged_bytes': max(sizes), 'disk_cap_bytes': 2147483648,
                       'measurement_scope': 'All staged files, inherited and new'}
        else:
            assert rows and all(len(row) == 4 for row in rows)
            physical = [int(float(row[1])) for row in rows]
            commit = [int(float(row[2])) for row in rows]
            working = [int(float(row[3])) for row in rows]
            assert min(physical) >= 1572864 and min(commit) >= 524288
            summary = {'samples': len(rows), 'first': rows[0][0], 'last': rows[-1][0],
                       'min_physical_KiB': min(physical), 'min_commit_free_KiB': min(commit),
                       'peak_working_set_bytes': max(working), 'stop_physical_KiB': 1572864, 'stop_commit_free_KiB': 524288}
        summary['original_immutable_sample_sha256'] = identity['sha256']
        summary['disposition'] = 'Resource DATA summary; raw samples retained in immutable original packet, omitted from compact transport'
        write('resource-json/' + Path(rel).stem + '.json', summary)
        references[rel] = dict(identity, disposition='Raw resource sample intentionally omitted; exact original identity retained', summary='resource-json/' + Path(rel).stem + '.json')
        continue
    if args.packet == 'point-order' and rel.startswith('maintained-source/'):
        canonical = repo / 'circuits/ShielddSecurity' / Path(rel).name
        if canonical.exists() and sha(canonical) == identity['sha256']:
            # All inherited prime sources are tracked; fresh Point sources resolve
            # to the separately transported exact trace/endpoint snapshot.
            if Path(rel).stem.startswith('SubgroupPrimeNode') or Path(rel).stem == 'SubgroupOrderPrime06':
                references[rel] = dict(identity, repository_reference=canonical.relative_to(repo).as_posix(),
                                       publication_head='7ea375d0f6e6f9eb5b3ddcb24341e60fcd734cef')
                continue
            if (trace / rel).exists() and sha(trace / rel) == identity['sha256']:
                references[rel] = dict(identity, packet_reference='point-trace-complete', packet_path=rel,
                                       original_trace_manifest_sha256=sha(trace / 'manifest.json'))
                continue
    copy(path, rel)

copy(source / 'manifest.json', 'inherited/original-frozen-manifest.json')
copy(Path(__file__), 'recipes/' + Path(__file__).name)
write('transport-references.json', references)
write('manifest.json', {'kind': 'Fresh compact immutable transport successor; original manifest preserved exactly',
      'files': dict(files), 'references': references, 'original_manifest_sha256': sha(source / 'manifest.json'),
      'scope': 'Complete successful pp.all type/axiom texts, sources, guards, resource JSON, supported isolated replay; no raw build/resource logs or composed caches',
      'new_kernel_or_control_credit': 0, 'full_transfer': 'OPEN'})
archive = local / (args.packet + '-compact-review-packet-20261009-03-utf8.json.xz')
meta = local / (args.packet + '-final-transport-20261009-03.json')
assert not archive.exists() and not meta.exists()
payload = {'files': {rel: (dest / rel).read_bytes().decode('utf-8') for rel in files}}
archive.write_bytes(lzma.compress(json.dumps(payload, separators=(',', ':')).encode()))
encoded = base64.b64encode(archive.read_bytes()).decode()
result = {'marker': 'TRANSFER_POINT_COMPACT_FINAL_REVIEW_TRANSPORT_METADATA_V1', 'packet': args.packet,
          'archive': str(archive), 'encoding': 'lzma-json-utf8-exact-files', 'sha256': sha(archive),
          'bytes': archive.stat().st_size, 'manifest_sha256': sha(dest / 'manifest.json'),
          'original_manifest_sha256': sha(source / 'manifest.json'), 'files': len(files), 'references': len(references),
          'chunks': (len(encoded) + 7999) // 8000, 'base64_chars_per_chunk': 8000,
          'original_manifests_unchanged': True, 'full_transfer': 'OPEN'}
meta.write_bytes((json.dumps(result, indent=2) + '\n').encode())
print(json.dumps(result))
