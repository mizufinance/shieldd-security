"""Resolve every actual direct import and recursive Lean header; source/objects are read-only."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PACKAGES = Path('C:/src/shieldd-formal/circuits/.lake/packages')
TOOLCHAIN = Path('C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0')
CACHE = DIAG / 'transfer-implementation-20261002/windows-jubjub-isolated-05/modules'
REFERENCE = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/receipts/mac/mac-connected-subgroup01/final01/official-imports-0a705f66a48b6c53.json')
REFERENCE_DATA = json.loads(REFERENCE.read_text())
PACKAGE_MAP = {'Mathlib': 'mathlib', 'Aesop': 'aesop', 'Batteries': 'batteries', 'Qq': 'Qq', 'Plausible': 'plausible',
    'ProofWidgets': 'proofwidgets', 'LeanSearchClient': 'LeanSearchClient', 'ImportGraph': 'importGraph', 'Cli': 'Cli'}
def pin(p):
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
def code_only(text):
    out = []; i = 0; depth = 0; line = False; string = False
    while i < len(text):
        pair, char = text[i:i+2], text[i]
        if line:
            out.append('\n' if char == '\n' else ' ')
            if char == '\n': line = False
            i += 1
        elif depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if char == '\n' else ' '); i += 1
        elif string:
            if char == '\\' and i + 1 < len(text): out.extend('  '); i += 2
            else:
                if char == '"': string = False
                out.append('\n' if char == '\n' else ' '); i += 1
        elif pair == '--': line = True; out.extend('  '); i += 2
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif char == '"': string = True; out.append(' '); i += 1
        else: out.append(char); i += 1
    # Only the header before the first declaration is consumed below. Body
    # character literals can contain quotes; their masking cannot affect the
    # already produced header prefix and is not a body-parsing claim.
    return ''.join(out)
def header(text):
    imports = []; prelude = False
    for line in code_only(text).splitlines():
        line = line.strip()
        if not line or line == 'module': continue
        if line == 'prelude': prelude = True; continue
        match = re.fullmatch(r'(?:(?:public|private|protected|meta)\s+)*import(?:\s+all)?\s+(.+)', line)
        if not match: break
        names = match.group(1).split()
        assert all(re.fullmatch(r'[A-Za-z0-9_.]+', n) for n in names), line
        imports.extend(names)
    return imports, not prelude
assert header('/- outer\npublic import Fake\n/- nested -/ -/\nmodule -- comment\npublic import all Mathlib.Real\nmeta import Lean.Real\nnamespace X\n') == (['Mathlib.Real', 'Lean.Real'], True)
sources = []
for name in ['transfer-floor-qualified-20261010-01', 'transfer-group-qualified-20261010-01']:
    sources += [q['source'] for q in json.loads((DIAG / name / 'qualification.json').read_text())['qualified']]
# Pending semantic modules need a separate expanded official-cache inventory;
# this task qualifies only the already built prerequisite/Group/symbolic scope.
sources += [t['source'] for t in json.loads((DIAG / 'transfer-torsion-cardinality49-20261010-02/plan.json').read_text())['targets']]
direct = {}
seeds = set()
for item in sources:
    assert pin(Path(item['path'])) == item
    imports, implicit = header(Path(item['path']).read_text())
    direct[item['path']] = imports
    seeds.update(n for n in imports if not n.startswith('ShielddSecurity.'))
    if implicit: seeds.add('Init')
modules = {}; files = {}; gaps = []; active = set()
def visit(module):
    if module in modules: return
    assert module not in active, 'Module cycle: ' + module
    active.add(module)
    prefix = module.split('.')[0]
    relative = module.replace('.', '/')
    builtin = prefix in ('Init', 'Lean', 'Std')
    if builtin:
        source = TOOLCHAIN / 'src/lean' / (relative + '.lean')
        object_root = TOOLCHAIN / 'lib/lean'
        package = None
    else:
        package = PACKAGE_MAP[prefix]
        source = PACKAGES / package / (relative + '.lean')
        object_root = CACHE
    if not source.is_file(): gaps.append({'module': module, 'reason': 'missing canonical source', 'path': str(source)}); active.remove(module); return
    source_pin = pin(source)
    if not builtin:
        key = package + '/' + relative + '.lean'
        if REFERENCE_DATA['files'].get(key) != source_pin['sha256']:
            gaps.append({'module': module, 'reason': 'canonical source absent/mismatched official reference', 'key': key})
    imports, implicit = header(source.read_text(encoding='utf-8'))
    objects = []
    for suffix in ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir']:
        path = object_root / (relative + suffix)
        if not path.is_file():
            if suffix.startswith('.olean'): gaps.append({'module': module, 'reason': 'missing required object', 'path': str(path)})
            continue
        record = pin(path)
        if not builtin:
            key = package + '/.lake/build/lib/lean/' + relative + suffix
            expected = REFERENCE_DATA['files'].get(key)
            if suffix.startswith('.olean') and expected != record['sha256']:
                gaps.append({'module': module, 'reason': 'object absent/mismatched official reference', 'key': key})
            elif expected is not None and expected != record['sha256']:
                gaps.append({'module': module, 'reason': 'auxiliary object mismatched existing official reference', 'key': key})
        objects.append(record)
    modules[module] = {'source': source_pin, 'objects': objects, 'imports': imports, 'implicit_Init': implicit}
    for record in [source_pin] + objects: files[record['path']] = record
    for dependency in imports + (['Init'] if implicit else []): visit(dependency)
    active.remove(module)
for seed in sorted(seeds): visit(seed)
result = {'kind': 'COMPLETE_ACTUAL_DIRECT_AND_RECURSIVE_IMPORT_IDENTITY_INVENTORY',
    'admission_ready': not gaps, 'gaps': gaps, 'modules': modules, 'immutable_files': list(files.values()),
    'official_reference': pin(REFERENCE), 'direct_source_imports': direct, 'root_modules': sorted(seeds),
    'parser': 'Nested comments and strings masked; complete actual root imports; module/prelude/public/meta/import-all headers parsed; implicit Init included.',
    'scope': 'Actual prerequisite/Group/symbolic external identity inventory only. Sources and required olean/private/server objects must match official reference; optional local ir/ilean absent from reference are pinned current-host auxiliaries, not semantic correspondence claims. Pending semantic imports deferred. Prior incomplete packets retained; fresh affected builds required.'}
(ROOT / 'external-floor.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) < 16 * 1024**2
print(json.dumps({'inventory': pin(ROOT / 'external-floor.json'), 'roots': sorted(seeds), 'modules': len(modules), 'files': len(files),
    'existing_bytes_pinned': sum(p['bytes'] for p in files.values()), 'admission_ready': not gaps, 'gaps': gaps[:20], 'gap_count': len(gaps)}))
