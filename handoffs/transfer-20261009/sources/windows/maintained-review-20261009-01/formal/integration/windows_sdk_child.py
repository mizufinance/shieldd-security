"""Root-only fresh Windows source child; no build, install, or observations.

The root must first supply a complete actual, byte-preserving source11 Windows
parent with its retained full inventory. This adapter never substitutes a clean
SDK checkout for the observed source11 lineage. Linux staging remains unchanged.
"""
from pathlib import Path
import hashlib
import importlib
import json
import shutil
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    require(path.is_file() and not path.is_symlink(), 'regular source required: ' + str(path))
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(65536), b''):
            h.update(data)
    return h.hexdigest()


def inventory(root):
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'source symlink refused')
        if path.is_file():
            result[path.relative_to(root).as_posix()] = sha(path)
    return result


def frozen_module(packet, relative_root, name):
    # Each phase uses its own frozen relative-import closure, not mutable origins.
    for key in list(sys.modules):
        if key == 'integration' or key.startswith('integration.'):
            del sys.modules[key]
    previous = list(sys.path)
    sys.path.insert(0, str(packet / relative_root))
    try:
        return importlib.import_module('integration.' + name)
    finally:
        sys.path[:] = previous


def checked_packet(packet, descriptor):
    require(sha(packet / descriptor['identity']) == descriptor['sha256'], 'frozen packet identity drift')
    data = json.loads((packet / descriptor['identity']).read_bytes())
    files = data['files'] if descriptor['identity'] == 'manifest.json' else data
    for path, wanted in files.items():
        require(sha(packet / path) == wanted, 'frozen resource drift: ' + path)
    return data


def instrument(source, prefix, observer, operations, resources, fragment):
    result = {}
    for relative, function in operations:
        path = prefix + relative
        require(path in source, 'missing exact source hook input: ' + path)
        result[path] = getattr(observer, function)(source[path])
    exporter = prefix + 'examples/transfer-ownership-inspection.rs'
    result[exporter] = observer.instrument_exporter(source[exporter], fragment)
    for path, body in resources.items():
        require(path not in source, 'new observer resource already present: ' + path)
        result[path] = body
    return result


def prepare(spec):
    require(sys.platform == 'win32', 'Windows-owned source adapter only')
    require(spec['runtime_pin'] == '844389ee069e1fb2e576708842d0b389b4d9a44a', 'exact runtime pin required')
    parent, child, receipt = map(Path, (spec['parent'], spec['child'], spec['receipt']))
    require(parent.is_dir() and not parent.is_symlink() and not child.exists() and not receipt.exists(), 'actual parent and fresh child/receipt required')
    require(child.parent.resolve() == parent.parent.resolve(), 'private sibling child required')
    require(not (parent / '.git').exists() and not (parent / 'target').exists(), 'source-only parent required')
    parent_inventory = Path(spec['parent_inventory'])
    require(sha(parent_inventory) == spec['parent_inventory_sha256'], 'actual root parent inventory changed')
    before = inventory(parent)
    require(before == json.loads(parent_inventory.read_bytes()), 'complete actual source11 parent differs')
    preserved = Path(spec['preserved_d931'])
    require(sha(preserved) == 'd9312aeb7ac92cd8c246c5a014bd71f8173378b6c0d9c9debc1f542172dea7f5', 'adopt exact previously preserved Linux binary first')
    packets = {name: Path(value['path']) for name, value in spec['packets'].items()}
    manifests = {name: checked_packet(packets[name], value) for name, value in spec['packets'].items()}
    broad = packets['broad']
    broad_recipe = json.loads((broad / 'recipe.json').read_bytes())
    require(broad_recipe['runtime_commit'] == spec['runtime_pin'], 'broad parent pin differs')
    # Full original observed source scope and path sets are retained verbatim.
    scoped = {}
    for line in (broad / 'parent-final-inventory.sha256').read_text().splitlines():
        wanted, relative = line.split(None, 1)
        relative = relative.lstrip('* ')
        require(relative not in scoped and before.get(relative) == wanted, 'source11 scoped identity differs: ' + relative)
        scoped[relative] = wanted
    for directory in broad_recipe['audited_source_directories']:
        actual = {p for p in before if p.startswith(directory + '/') and p.endswith('.rs')}
        expected = {p for p in scoped if p.startswith(directory + '/') and p.endswith('.rs')}
        require(actual == expected, 'source11 observed source path set differs')
    source = {path: (parent / path).read_bytes() for path in scoped if path.endswith('.rs')}
    prefix = 'crates/crypto/circuits/'
    phases = []
    observer = frozen_module(broad, 'lib', 'transfer_remaining_observer')
    broad_inputs = set(observer.hooks()) | {observer.CATALOGUE, observer.EXPORTER}
    addition = observer.compose({path: source[path] for path in broad_inputs})
    require({path for path in addition if source.get(path) != addition[path]} == set(broad_recipe['exact_changed_paths']), 'broad composition ownership differs')
    phases.append(('broad', addition)); source.update(addition)
    variable = packets['variable']
    observer = frozen_module(variable, 'source', 'balance_variable_observer')
    resource_root = variable / 'source/integration/observers'
    resources = {prefix + 'src/group/balance_variable_inspection.rs': (resource_root / 'balance_variable.rs').read_bytes(),
                 prefix + 'src/balance_variable_catalogue.rs': (resource_root / 'balance_variable_catalogue.rs').read_bytes()}
    # Exact original variable fragment plus reviewed five-page fragment, in that order.
    fragment = (resource_root / 'balance_variable_export.rs').read_bytes() + b'\n' + (resource_root / 'balance_variable_pages_export.rs').read_bytes()
    addition = instrument(source, prefix, observer, [('src/group.rs','instrument_group'), ('src/balance.rs','instrument_balance'), ('src/catalogue.rs','instrument_catalogue')], resources, fragment)
    phases.append(('variable', addition)); source.update(addition)
    epk = packets['epk']
    observer = frozen_module(epk, 'lib', 'epk_fixed_observer')
    resources = {prefix + 'src/group/epk_fixed_inspection.rs': (epk / 'lib/integration/observers/epk_fixed.rs').read_bytes(),
                 prefix + 'src/epk_fixed_catalogue.rs': (epk / 'lib/integration/observers/epk_fixed_catalogue.rs').read_bytes()}
    addition = instrument(source, prefix, observer, [('src/group.rs','instrument_group'), ('src/recovery.rs','instrument_recovery'), ('src/encryption.rs','instrument_encryption'), ('src/catalogue.rs','instrument_catalogue')], resources, (epk / 'lib/integration/observers/epk_fixed_export.rs').read_bytes())
    epk_expected = manifests['epk']['variants']['balance-sibling']['changed']
    require(set(addition) == set(epk_expected), 'exact EPK sibling ownership differs')
    for path, body in addition.items():
        require(hashlib.sha256(source[path]).hexdigest() == epk_expected[path]['before'] if path in source else epk_expected[path]['before'] is None, 'EPK actual beforehash differs: ' + path)
        require(hashlib.sha256(body).hexdigest() == epk_expected[path]['after'], 'EPK sibling composition differs: ' + path)
    phases.append(('epk', addition)); source.update(addition)
    blinding = packets['blinding']
    observer = frozen_module(blinding, 'lib', 'balance_blinding_observer')
    resources = {prefix + 'src/group/balance_blinding_fixed_inspection.rs': (blinding / 'lib/integration/observers/balance_blinding_fixed.rs').read_bytes(),
                 prefix + 'src/balance_blinding_fixed_catalogue.rs': (blinding / 'lib/integration/observers/balance_blinding_fixed_catalogue.rs').read_bytes()}
    addition = instrument(source, prefix, observer, [('src/group.rs','instrument_group'), ('src/balance.rs','instrument_balance'), ('src/catalogue.rs','instrument_catalogue')], resources, (blinding / 'lib/integration/observers/balance_blinding_fixed_export.rs').read_bytes())
    require(set(addition) == set(manifests['blinding']['changed']) and len(addition) == 6, 'exact six blinding overlays required')
    for path, body in addition.items():
        change = manifests['blinding']['changed'][path]
        require(hashlib.sha256(source[path]).hexdigest() == change['before'] if path in source else change['before'] is None, 'blinding actual beforehash differs: ' + path)
        require(hashlib.sha256(body).hexdigest() == change['after'] and body == (blinding / 'overlay' / path).read_bytes(), 'exact six blinding composition differs: ' + path)
    phases.append(('blinding', addition)); source.update(addition)
    expected = dict(before)
    for name, addition in phases:
        expected.update({path: hashlib.sha256(body).hexdigest() for path, body in addition.items()})
    # Refusal above creates no stage. All phases retain the complete exporter.
    receipt.mkdir(); shutil.copytree(parent, child)
    require(inventory(child) == before, 'private copy identity differs')
    for name, addition in phases:
        for path, body in addition.items():
            destination = child / path; destination.parent.mkdir(parents=True, exist_ok=True); destination.write_bytes(body)
    require(inventory(child) == expected and inventory(parent) == before, 'source inventory closure differs')
    for name, value in [('parent-before.json',before), ('parent-after.json',before), ('child-after.json',expected), ('phases.json',[{ 'name': name, 'changed': {path: hashlib.sha256(body).hexdigest() for path, body in addition.items()} } for name, addition in phases])]:
        (receipt / name).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
    (receipt / 'complete.txt').write_text('Fresh Windows source child only; runtime and backend correspondence UNRUN.\n')
    return expected


if __name__ == '__main__':
    require(len(sys.argv) == 2, 'one exact root activation spec required')
    prepare(json.loads(Path(sys.argv[1]).read_bytes()))
