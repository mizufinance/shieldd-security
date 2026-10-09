from pathlib import Path
body = Path('C:/src/shieldd-transfer-handoffs/prepare-windows-subgroup-arithmetic-20261009-03.py').read_text()
body = body.replace('windows-subgroup-arithmetic-20261009-03', 'windows-connected-subgroup-semantics-20261009-01')
body = body.replace('GroupSubgroupGraphArithmetic', 'TransferFirstSubgroupSemantics01')
body = body.replace('sources, order, expected, candidates = {}, [], {}, {}', '''sources, order, expected, candidates = {}, [], {}, {}
reused, receipts, sealed_inputs = [], {}, []
published = Path('C:/src/shieldd-transfer-windows-publication-20261009/handoffs/transfer-20261009/sources/mac/mac-connected-subgroup01/final01/project/ShielddSecurity')
for namespace in ['windows-subgroup-source-graph-20261009-05', 'windows-subgroup-arithmetic-20261009-03']:
    sealed = diag / (namespace + '-kernel')
    assert (sealed / 'complete.txt').exists() and (sealed / 'end.txt').exists()
    assert (sealed / 'exit.txt').read_text().strip() == '0'
    checked = json.loads((sealed / 'manifest.json').read_text(encoding='utf-8-sig'))
    sealed_inputs.append((sealed, checked))
    for key in ['manifest.json', 'recipe.json', 'complete.txt', 'exit.txt', 'end.txt']:
        receipts[str(sealed / key)] = sha(sealed / key)
''')
body = body.replace("    p = src / (name + '.lean')", '''    p = published / (name + '.lean')
    if not p.exists(): p = src / (name + '.lean')''', 1)
body = body.replace("    raw = p.read_bytes()", '''    for sealed, checked in sealed_inputs:
        if name not in checked['sources'] or sha(p) != checked['sources'][name]['sha256']: continue
        audit = sealed / name / 'audit.json'
        assert audit.exists()
        audited_source = sealed / 'project/ShielddSecurity' / (name + '.lean')
        object_path = audited_source.with_suffix('.olean')
        assert sha(audited_source) == checked['audited_candidates'][name]
        assert object_path.exists()
        item = {'name': name, 'source': str(audited_source), 'source_sha256': sha(audited_source),
                'object': str(object_path), 'object_sha256': sha(object_path),
                'original_source': str(p), 'original_source_sha256': sha(p)}
        if item not in reused: reused.append(item)
        receipts[str(audit)] = sha(audit)
        for dependency in checked['sources'][name]['imports']:
            if dependency.startswith('ShielddSecurity.'): visit(dependency.split('.', 1)[1])
        return
    raw = p.read_bytes()''', 1)
body = body.replace("    p = src / (name + '.lean')", "    p = Path(sources[name]['path'])")
body = body.replace("    assert names and len(names) == len(set(names)), name", "    assert len(names) == len(set(names)), name\n    assert names or name in ['TransferFirstSubgroupTables01', 'TransferFirstSubgroupTables02'], name")
body = body.replace("'reused': [], 'frozen_import_receipts': {}", "'reused': reused, 'frozen_import_receipts': receipts")
old_scope = next(line for line in body.splitlines() if line.startswith('scope = '))
body = body.replace(old_scope, "scope = 'Concrete first registry dk: exact published SourceGraph 22735 80 syntax match, all six independent source assertions, actual71 original-row arbitrary-assignment soundness, and native constructor satisfying those rows while preserving22735 inputs. Independent subgroup admission constructs SDK preimage and shared inverse hints; identity permitted. Two/four nonzero derived from characteristic. Named curve/codec/Crypto deployment, other full Transfer graph blocks and native/state refinement remain OPEN.'")
Path('C:/src/shieldd-transfer-handoffs/prepare-windows-connected-subgroup-semantics-20261009-01.py').write_text(body)
