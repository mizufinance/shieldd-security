"""Test-only native loader delta and exact private child for the live codec join.

Root runs staging and native tests after its existing capture queue. This module
does not run Cargo, access native keys, or change any shared source child.
"""
from pathlib import Path
import hashlib
import json
import shutil
import sys

from integration.balance_native_compile_repair import inventory, sha

RELATIVE = 'crates/crypto/primitives/src/poseidon.rs'
PARENT_SHA = 'f59fa7f8d9c2ea2a6534a9ec7c175c72dccb3de6f9dc5b2247f9d3d82776a2e0'


def append_controls(data, resource):
    if type(data) is not bytes or type(resource) is not bytes:
        raise ValueError('exact source/resource bytes required')
    if hashlib.sha256(data).hexdigest() != PARENT_SHA:
        raise ValueError('pinned production source required')
    if not resource.startswith(b'\n#[cfg(test)]\nmod formal_parameter_loader_controls {'):
        raise ValueError('isolated cfg(test) control module required')
    if resource.count(b'#[test]') != 7 or b'formal_parameter_loader_controls' in data:
        raise ValueError('exact seven new controls required')
    return data + resource


def portable(raw):
    path = raw.replace('\\', '/')
    return Path('/mnt/c/' + path[3:]) if sys.platform != 'win32' and path.startswith('C:/') else Path(raw)


def prepare(packet):
    packet = Path(packet)
    manifest = json.loads((packet / 'manifest.json').read_bytes())
    for relative, digest in manifest['files'].items():
        if sha(packet / relative) != digest:
            raise ValueError('frozen control source changed')
    for raw, digest in manifest['inputs'].items():
        if sha(portable(raw)) != digest:
            raise ValueError('exact parent/source receipt changed')
    # This actual completed queue is a live prerequisite, not a frozen future receipt.
    complete = portable(manifest['deferred_parent_complete'])
    if not complete.is_file() or complete.is_symlink():
        raise ValueError('root capture queue must finish before private child staging')
    parent, child, receipt = map(Path, (manifest['parent'], manifest['child'], manifest['receipt']))
    if not parent.is_dir() or child.exists() or receipt.exists() or child.parent.resolve() != parent.parent.resolve():
        raise ValueError('exact parent and fresh owned child/receipt required')
    if (parent / '.git').exists() or (parent / 'target').exists():
        raise ValueError('source-only parent required')
    expected = json.loads(portable(manifest['parent_inventory']).read_bytes())
    before = inventory(parent)
    if before != expected:
        raise ValueError('complete actual parent inventory changed')
    data = append_controls((parent / RELATIVE).read_bytes(),
        (packet / 'native_parameter_loader_controls.rs').read_bytes())
    change = manifest['changed'][RELATIVE]
    if before[RELATIVE] != change['before'] or hashlib.sha256(data).hexdigest() != change['after']:
        raise ValueError('exact appended test delta changed')
    if data != (packet / 'overlay' / RELATIVE).read_bytes():
        raise ValueError('frozen overlay differs')
    receipt.mkdir()
    shutil.copytree(parent, child)
    if inventory(child) != before:
        raise ValueError('private source copy identity differs')
    (child / RELATIVE).write_bytes(data)
    after = dict(before)
    after[RELATIVE] = hashlib.sha256(data).hexdigest()
    if inventory(child) != after or inventory(parent) != before:
        raise ValueError('production prefix or unrelated source changed')
    for name, value in [('parent-before.json', before), ('parent-after.json', before),
                        ('child-after.json', after), ('changed.json', manifest['changed'])]:
        (receipt / name).write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')
    with (receipt / 'final-inventory.sha256').open('x') as stream:
        for relative, digest in sorted(after.items()):
            stream.write(digest + '  ' + relative + '\n')
    (receipt / 'complete.txt').write_text('Exact test-only source child; native test results UNRUN.\n')
    return after


def verify(packet, output):
    packet = Path(packet)
    manifest = json.loads((packet / 'manifest.json').read_bytes())
    for relative, digest in manifest['files'].items():
        if sha(packet / relative) != digest:
            raise ValueError('frozen native control source changed')
    for raw, digest in manifest['inputs'].items():
        if sha(portable(raw)) != digest:
            raise ValueError('native control ancestry changed')
    receipt = Path(manifest['receipt'])
    if not (receipt / 'complete.txt').is_file():
        raise ValueError('actual private child staging required')
    before = json.loads((receipt / 'parent-before.json').read_bytes())
    after = json.loads((receipt / 'child-after.json').read_bytes())
    if inventory(Path(manifest['parent'])) != before or inventory(Path(manifest['child'])) != after:
        raise ValueError('complete parent/child source inventory changed')
    if set(before) != set(after) or {p for p in after if before[p] != after[p]} != {RELATIVE}:
        raise ValueError('only test-only poseidon delta allowed')
    parent_bytes = (Path(manifest['parent']) / RELATIVE).read_bytes()
    child_bytes = (Path(manifest['child']) / RELATIVE).read_bytes()
    if child_bytes != append_controls(parent_bytes, (packet / 'native_parameter_loader_controls.rs').read_bytes()):
        raise ValueError('production prefix/test delta changed')
    output = Path(output)
    if output.exists():
        raise ValueError('fresh full source snapshot required')
    output.write_text(json.dumps(after, sort_keys=True, indent=2) + '\n')
    return after


if __name__ == '__main__':
    if len(sys.argv) == 2:
        prepare(sys.argv[1])
    elif len(sys.argv) == 4 and sys.argv[2] == '--verify':
        verify(sys.argv[1], sys.argv[3])
    else:
        raise ValueError('one frozen packet; optional --verify fresh-snapshot path')
