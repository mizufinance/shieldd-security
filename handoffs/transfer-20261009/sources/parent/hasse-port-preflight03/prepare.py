"""Prepare an unbuilt, auditable Hasse source subset at the campaign pin.

Only removes complete unused declaration ranges and maps two renamed imports.
No theorem conclusion or proof body retained in the subset is weakened.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
from inventory import ARCHIVE, HERE, REMAP, code_only

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    if not __debug__:
        raise RuntimeError('optimized Python forbidden')
    preflight = json.loads((HERE / 'preflight.json').read_text())
    recipe = json.loads((HERE / 'omission-recipe.json').read_text())
    assert recipe['commit'] == preflight['external_commit']
    out = HERE / 'prepared'
    assert not out.exists(), 'refusing to replace an existing prepared snapshot'
    root = Path(recipe['root'])
    sources, removed, mapped = {}, [], []
    for module, entry in preflight['source_nodes'].items():
        path = ARCHIVE / entry['path']
        original = path.read_bytes()
        assert digest(original) == entry['sha256']
        lines = original.decode().splitlines(keepends=True)
        omit = [item for item in recipe['omit_ranges']
                if root / item['file'] == Path(entry['path'])]
        occupied = set()
        for item in omit:
            lo, hi = item['start'] - 1, item['end']
            assert 0 <= lo < hi <= len(lines)
            assert not occupied.intersection(range(lo, hi))
            occupied.update(range(lo, hi))
            old = ''.join(lines[lo:hi])
            names = re.findall(r'^(?:private |protected |noncomputable )*'
                r'(?:theorem|lemma|def)\s+(\S+)', code_only(old), re.M)
            assert names, item
            removed.append(dict(module=module, original_path=entry['path'],
                start=item['start'], end=item['end'], declarations=names,
                omitted_text_sha256=digest(old.encode())))
            lines[lo:hi] = ['-- Port subset: unused incomplete declarations omitted.\n'] + [
                '\n'] * (hi - lo - 1)
        text = ''.join(lines)
        for old, new in REMAP.items():
            pattern = r'^(\s*(?:(?:public|meta)\s+)*import\s+)' + re.escape(old) + r'\s*$'
            text, count = re.subn(pattern, lambda match: match[1] + new, text, flags=re.M)
            if count:
                mapped.append(dict(module=module, original=old, target=new, count=count))
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', code_only(text)), module
        relative = Path(*module.split('.')).with_suffix('.lean')
        sources[module] = dict(relative_path=str(relative), original_path=entry['path'],
            original_sha256=digest(original), prepared_sha256=digest(text.encode()),
            bytes=len(text.encode()), changed=text.encode() != original, text=text)
    names = {name for item in removed for name in item['declarations']}
    dangling = []
    for module, source in sources.items():
        code = code_only(source['text'])
        for name in names:
            if re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", code):
                dangling.append(dict(module=module, name=name))
    assert not dangling, dangling
    capstone = sources['HasseWeil.HasseBound']
    assert capstone['prepared_sha256'] == capstone['original_sha256']
    for module, source in sources.items():
        dest = out / source['relative_path']
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(source.pop('text'))
    shutil.copyfile(ARCHIVE / 'LICENSE', out / 'LICENSE')
    report = dict(kind='unbuilt-external-source-subset',
        external_commit=recipe['commit'],
        campaign_mathlib=preflight['campaign_mathlib'],
        recipe_sha256=digest((HERE / 'omission-recipe.json').read_bytes()),
        preparation_script_sha256=digest(Path(__file__).read_bytes()),
        sources=sources, removed=removed, mapped_imports=mapped,
        dangling_name_references=dangling, capstone_byte_identical=True,
        license_sha256=digest((out / 'LICENSE').read_bytes()),
        kernel_run=False, kernel_credit=0,
        limits=['Lexical name tracing cannot replace elaboration or axiom auditing.',
                'Foreign comments still describe omitted declarations; they are not proof claims.',
                'API compatibility and resource feasibility on Lean4.30 are unqualified.'],
        full_transfer='OPEN')
    (HERE / 'prepared-manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    print(len(sources), 'sources;', len(removed), 'omitted ranges;',
          len(names), 'omitted declarations;', len(mapped), 'mapped imports; no kernel run')

if __name__ == '__main__':
    main()
