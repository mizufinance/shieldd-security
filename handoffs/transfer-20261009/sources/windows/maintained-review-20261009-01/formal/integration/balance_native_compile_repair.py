"""Exact three-error source repair after the actual native unit compiler failure.

This is not a runtime test/control. Root-only staging copies the failed child
before applying two changed-file overlays; all other source bytes are retained.
"""
from pathlib import Path
import hashlib
import json
import shutil
import sys

BALANCE = 'crates/crypto/circuits/src/balance.rs'
FIXTURE = 'crates/crypto/circuits/src/note/output_hash_inspection.rs'


def repair_balance(data):
    before = b'let balance_blinding_scope = group::balance_blinding_fixed_inspection::scope('
    after = b'let balance_blinding_scope = crate::group::balance_blinding_fixed_inspection::scope('
    if not isinstance(data, bytes) or data.count(before) != 1 or after in data:
        raise ValueError('exact failed blinding module path required')
    return data.replace(before, after)


def repair_fixture(data):
    marker = b'#[cfg(test)]'
    if not isinstance(data, bytes) or data.count(marker) != 1:
        raise ValueError('one owned fixture section required')
    production, tests = data.split(marker)
    for before, after in [
        (b'note:values(8).iter().map(observed).collect::<Vec<_>>().try_into().unwrap()',
         b'note:values(8).iter().map(observed).collect::<Vec<_>>().try_into().ok().expect("eight fixture note fields")'),
        (b'capsule:values(7).iter().map(observed).collect::<Vec<_>>().try_into().unwrap()',
         b'capsule:values(7).iter().map(observed).collect::<Vec<_>>().try_into().ok().expect("seven fixture capsule fields")')]:
        if tests.count(before) != 1 or before in production or after in tests:
            raise ValueError('exact failed observed-array fixture conversion required')
        tests = tests.replace(before, after)
    return production + marker + tests


def sha(path):
    if not path.is_file() or path.is_symlink():
        raise ValueError('regular retained input required')
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(65536), b''):
            digest.update(data)
    return digest.hexdigest()


def inventory(root):
    result = {}
    for path in sorted(root.rglob('*')):
        if path.is_symlink():
            raise ValueError('source symlink refused')
        if path.is_file():
            result[path.relative_to(root).as_posix()] = sha(path)
    return result


def prepare(packet):
    packet = Path(packet)
    manifest = json.loads((packet / 'manifest.json').read_bytes())
    for relative, digest in manifest['files'].items():
        if sha(packet / relative) != digest:
            raise ValueError('frozen repair source changed')
    for raw, digest in manifest['inputs'].items():
        portable = raw.replace('\\', '/')
        path = Path('/mnt/c/' + portable[3:]) if sys.platform != 'win32' and portable.startswith('C:/') else Path(raw)
        if sha(path) != digest:
            raise ValueError('actual failure/first-five receipt identity changed')
    parent, child, receipt = map(Path, (manifest['parent'],manifest['child'],manifest['receipt']))
    if not parent.is_dir() or child.exists() or receipt.exists() or child.parent.resolve() != parent.parent.resolve() or (parent / '.git').exists() or (parent / 'target').exists():
        raise ValueError('failed source parent and fresh private child/receipt required')
    expected = json.loads(Path(manifest['parent_inventory']).read_bytes())
    before = inventory(parent)
    if before != expected:
        raise ValueError('actual failed child inventory changed')
    replacements = {BALANCE:repair_balance((parent / BALANCE).read_bytes()), FIXTURE:repair_fixture((parent / FIXTURE).read_bytes())}
    for relative, data in replacements.items():
        change = manifest['changed'][relative]
        if before[relative] != change['before'] or hashlib.sha256(data).hexdigest() != change['after'] or data != (packet / 'overlay' / relative).read_bytes():
            raise ValueError('exact three compiler fixes differ from retained source')
    receipt.mkdir(); shutil.copytree(parent, child)
    if inventory(child) != before:
        raise ValueError('private source copy identity differs')
    for relative, data in replacements.items():
        (child / relative).write_bytes(data)
    after = dict(before); after.update({relative: hashlib.sha256(data).hexdigest() for relative,data in replacements.items()})
    if inventory(child) != after or inventory(parent) != before:
        raise ValueError('source closure changed beyond the two files')
    for name,value in [('parent-before.json',before),('parent-after.json',before),('child-after.json',after),('changed.json',manifest['changed'])]:
        (receipt / name).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
    with (receipt / 'final-inventory.sha256').open('x') as output:
        for path,digest in sorted(after.items()):
            output.write(digest+'  '+path+'\n')
    (receipt / 'complete.txt').write_text('Source-only exact three compiler-error repairs; native tests/build/captures UNRUN.\n')
    return after


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('one frozen compiler repair packet required')
    prepare(sys.argv[1])
