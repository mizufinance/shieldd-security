"""Place formal-owned diagnostic binaries in a disposable locked runtime stage."""
from pathlib import Path
import hashlib
import json

EXPORTERS = ('transfer-relation', 'transfer-balance-inspection',
             'transfer-canonical-balance-inspection', 'transfer-ivk-inspection',
             'transfer-ivk-reduction-inspection', 'transfer-ak-subgroup-inspection',
             'transfer-ownership-inspection', 'transfer-baseline')

def _digest(path):
    if path.is_symlink():
        raise ValueError('staging inputs must not be symbolic links')
    return hashlib.sha256(path.read_bytes()).hexdigest()

def _inventory(root, relative):
    base = root / relative
    if base.is_symlink() or not base.is_dir():
        raise ValueError('missing or linked runtime source directory')
    entries = sorted(base.rglob('*'))
    if any(p.is_symlink() for p in entries):
        raise ValueError('runtime inventory must not contain symbolic links')
    return {p.relative_to(base).as_posix(): _digest(p) for p in entries if p.is_file()}

def prepare_exporters(source, stage):
    source, stage = Path(source).resolve(), Path(stage).resolve()
    if source == stage or (stage / '.git').exists() or not stage.is_dir():
        raise ValueError('exporter destination must be an existing disposable runtime stage')
    files = ('Cargo.toml', 'Cargo.lock', 'crates/crypto/circuits/Cargo.toml',
             'third_party/commonware/Cargo.lock',
             'third_party/commonware-patches/provenance.json')
    before = {name: _digest(source / name) for name in files}
    if before != {name: _digest(stage / name) for name in files}:
        raise ValueError('runtime stage manifest/lock/provenance mismatch')
    directories = ('crates/crypto/circuits/src', 'crates/crypto/primitives/src', 'crates/crypto/primitives/params',
                   'third_party/commonware/cryptography/src/zk')
    for root in (source, stage):
        for name in (*directories, 'crates/crypto/circuits/examples'):
            current = root
            for component in Path(name).parts:
                current /= component
                if current.is_symlink():
                    raise ValueError('runtime staging paths must not contain symbolic links')
    inventories = {name: _inventory(source, name) for name in directories}
    if inventories != {name: _inventory(stage, name) for name in directories}:
        raise ValueError('runtime stage selected source inventory mismatch')
    destination = stage / 'crates/crypto/circuits/examples'
    if destination.is_symlink():
        raise ValueError('exporter destination must not be linked')
    authored = Path(__file__).resolve().parent / 'src/bin'
    payloads = {name: (authored / (name + '.rs')).read_bytes() for name in EXPORTERS}
    for name, data in payloads.items():
        target = destination / (name + '.rs')
        if target.is_symlink() or (target.exists() and target.read_bytes() != data):
            raise ValueError('refusing to replace a divergent staged exporter')
    destination.mkdir(exist_ok=True)
    for name, data in payloads.items():
        target = destination / (name + '.rs')
        if not target.exists():
            with target.open('xb') as handle:
                handle.write(data)
    if (before != {name: _digest(source / name) for name in files}
            or before != {name: _digest(stage / name) for name in files}
            or inventories != {name: _inventory(source, name) for name in directories}
            or inventories != {name: _inventory(stage, name) for name in directories}):
        raise ValueError('runtime staging inputs drifted; retain diagnostic stage')
    hashes = {name: _digest(destination / (name + '.rs')) for name in EXPORTERS}
    if (hashes != {name: hashlib.sha256(data).hexdigest() for name, data in payloads.items()}
            or hashes != {name: _digest(authored / (name + '.rs')) for name in EXPORTERS}):
        raise ValueError('staged exporter bytes differ from formal-owned source')
    summaries = {name: {'files': len(inventory),
                        'sha256': hashlib.sha256(json.dumps(inventory, sort_keys=True,
                                                           separators=(',', ':')).encode()).hexdigest()}
                 for name, inventory in inventories.items()}
    return {'exporters': hashes, 'runtime_inputs': before, 'selected_source_inventories': summaries,
            'scope': 'diagnostic selected-source staging only; no build, runtime or qualification result'}
