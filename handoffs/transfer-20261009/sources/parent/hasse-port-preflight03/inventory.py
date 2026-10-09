"""Source-only Hasse port inventory. This does not invoke a compiler."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ARCHIVE = Path('/tmp/transfer-proof-implementation-20261009/hasse-reference')
MATHLIB = HERE.parents[1] / 'work/mac-volume-completion/project/.lake/packages/mathlib'
REMAP = {
    'Mathlib.RingTheory.ClassGroup.Basic': 'Mathlib.RingTheory.ClassGroup',
    'Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing':
        'Mathlib.RingTheory.Valuation.Discrete.Basic',
}

def code_only(source):
    output, position, depth = [], 0, 0
    while position < len(source):
        pair = source[position:position + 2]
        if pair == '/-':
            depth += 1
            output.extend('  ')
            position += 2
        elif depth and pair == '-/':
            depth -= 1
            output.extend('  ')
            position += 2
        elif depth:
            output.append('\n' if source[position] == '\n' else ' ')
            position += 1
        elif pair == '--':
            end = source.find('\n', position)
            end = len(source) if end < 0 else end
            output.extend(' ' * (end - position))
            position = end
        elif source[position] == '"':
            output.append(' ')
            position += 1
            while position < len(source):
                char = source[position]
                output.append('\n' if char == '\n' else ' ')
                position += 1
                if char == '\\' and position < len(source):
                    output.append(' ')
                    position += 1
                elif char == '"':
                    break
        else:
            output.append(source[position])
            position += 1
    assert depth == 0
    return ''.join(output)

def main():
    if not __debug__:
        raise RuntimeError('optimized Python forbidden')
    inventory = json.loads((ARCHIVE / 'qualified-inventory.json').read_text())
    files = inventory['source_files']
    nodes, external, unresolved = {}, {}, set()
    for name, identity in files.items():
        raw = (ARCHIVE / identity['path']).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == identity['sha256']
        source = code_only(raw.decode())
        imports = set(re.findall(
            r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)',
            source, re.M))
        own, others = sorted(imports & files.keys()), sorted(imports - files.keys())
        nodes[name] = dict(path=identity['path'], sha256=identity['sha256'],
            bytes=len(raw), owned_imports=own, external_imports=others,
            lexical_sorry_lines=[source[:m.start()].count('\n') + 1
                for m in re.finditer(r'\b(?:sorry|admit|axiom)\b', source)])
        for original in others:
            target = REMAP.get(original, original)
            path = MATHLIB / Path(*target.split('.')).with_suffix('.lean')
            if not path.exists():
                unresolved.add(original)
                continue
            users = sorted(set(external.get(original, {}).get('users', []) + [name]))
            external[original] = dict(target=target,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                source_path=str(path), users=users)
    order, visiting, seen = [], set(), set()
    def visit(name):
        if name in seen:
            return
        assert name not in visiting, name
        visiting.add(name)
        for child in nodes[name]['owned_imports']:
            visit(child)
        visiting.remove(name)
        seen.add(name)
        order.append(name)
    visit('HasseWeil.HasseBound')
    assert set(order) == set(nodes)
    result = dict(kind='source-only-port-preflight-no-build',
        external_commit=inventory['commit'],
        campaign_mathlib='c5ea00351c28e24afc9f0f84379aa41082b1188f',
        source_nodes=nodes, topological_order=order, external_sources=external,
        proposed_import_path_remaps=REMAP, unresolved_paths=sorted(unresolved),
        leaves=[name for name in order if not nodes[name]['owned_imports']],
        gate='Do not build this unmodified closure: five explicit sorry declarations '
             'must be excluded with their unused consumer declarations or proved. '
             'Source tracing is insufficient for capstone axiom qualification. '
             'No path remap has been applied or kernel checked.',
        kernel_credit=0, full_transfer='OPEN')
    (HERE / 'preflight.json').write_text(json.dumps(result, indent=2) + '\n')
    print(len(nodes), 'owned sources;', len(external), 'external sources;',
          len(unresolved), 'unresolved paths')

if __name__ == '__main__':
    main()
