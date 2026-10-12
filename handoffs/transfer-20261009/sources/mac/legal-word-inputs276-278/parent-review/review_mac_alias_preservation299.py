from pathlib import Path
import ast, difflib, hashlib, importlib.util, json, lzma, os, re, stat, subprocess

J = Path(__file__).parent
W = J.parent
S = W / 'mac-inactive-alias-storage275-source02'
manifest = S / 'aliases-manifest01.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
def pin(p):
    return dict(path=str(p), bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
def strict(raw):
    def pairs(items):
        result = {}
        for k, v in items:
            assert k not in result
            result[k] = v
        return result
    return json.loads(raw, object_pairs_hook=pairs)

assert pin(manifest) == dict(path=str(manifest), bytes=227285, sha256='b3a898cb4a03c14601e97d2539c4fca30225211b9bbe1e80db8c0408bbceb70c')
spec = importlib.util.spec_from_file_location('metadata', J/'read_preserved_mac_config20.py')
metadata = importlib.util.module_from_spec(spec)
spec.loader.exec_module(metadata)
record = strict(manifest.read_bytes())
assert set(record) == {'schema', 'directories', 'scope'} and record['schema'] == 'exact-inactive-input-alias-storage01'
assert len(record['directories']) == 266
targets = {}
links = total = packed = 0
recovery = []
for root, entry in sorted(record['directories'].items()):
    match = re.fullmatch(re.escape(str(W)) + r'/mac-full-arithmetic45-execution(\d+)/own-cache/ShielddSecurity', root)
    assert match and 1 <= int(match[1]) < 302
    assert entry['directory'] == root and set(entry) == {'directory','overlay','archive','decoded_bytes','decoded_sha256','links'}
    assert 0 < entry['decoded_bytes'] <= 16*1024**2 and 0 < entry['archive']['bytes'] <= 2*1024**2
    archive = Path(entry['archive']['path'])
    assert archive.is_relative_to(S/'archives') and archive.is_file() and not archive.is_symlink() and pin(archive) == entry['archive']
    decoder = lzma.LZMADecompressor(memlimit=128*1024**2)
    raw = decoder.decompress(archive.read_bytes(), max_length=entry['decoded_bytes']+1)
    assert decoder.eof and not decoder.unused_data and len(raw) == entry['decoded_bytes'] and sha(raw) == entry['decoded_sha256']
    data = strict(raw)
    assert set(data) == {'schema','directory','links'} and data['schema'] == 'exact-inactive-input-alias-root01' and data['directory'] == root
    assert len(data['links']) == entry['links']
    overlay = strict(metadata.read_original(entry['overlay']['path'], entry['overlay']))['aliases']
    assert {root+'/'+name:v['target'] for name,v in data['links'].items()} == overlay
    for name, v in data['links'].items():
        assert re.fullmatch(r'[A-Za-z0-9_]+\.(?:olean(?:\.private|\.server)?|ilean|ir)', name)
        assert set(v) == {'target','mode','mtime_ns','size'} and stat.S_ISLNK(v['mode']) and type(v['mtime_ns']) is int and v['mtime_ns'] >= 0
        assert v['size'] == len(os.fsencode(v['target']['path']))
        path = Path(root)/name
        assert not path.exists() and not path.is_symlink()
        target = v['target']
        if target['path'] in targets:
            assert targets[target['path']] == target
        else:
            p = Path(target['path'])
            assert p.is_file() and not p.is_symlink()
            with p.open('rb') as f:
                digest = hashlib.file_digest(f, 'sha256').hexdigest()
            assert p.stat().st_size == target['bytes'] and digest == target['sha256']
            targets[target['path']] = target
    links += len(data['links']); total += len(raw); packed += entry['archive']['bytes']
    recovery.append(entry)
assert links == 374900 and total == 133926903 and packed == 18524396
completed = list(S.glob('completed-root-*.json'))
assert len(completed) == 266
assert {strict(p.read_bytes())['directory'] for p in completed} == set(record['directories'])
for p in completed:
    value = strict(p.read_bytes())
    assert value == record['directories'][value['directory']]
plan = strict((S/'plan01.json').read_bytes())
assert len(plan['roots']) == 266 and {x['directory'] for x in plan['roots']} == set(record['directories'])
for e in plan['roots']:
    value = record['directories'][e['directory']]
    assert all(value[k] == e[k] for k in e)

baseline = W/'mac-full-arithmetic45-execution302/maintained/guard.py'
candidate = S/'guard-candidate.py'
deployed = W/'mac-full-arithmetic45-execution303/maintained/guard.py'
assert pin(baseline)['sha256'] == '77e05e4eb1caeb76f58bf3dbfd45ebd7107391ac26b8ef2b464842c6d4e96b21'
assert pin(candidate)['sha256'] == 'feba155f21f9d96f065dc75856e38154524f03ea3e119f241299aa0e36253676'
assert pin(deployed)['sha256'] == '888bb69348a545de15a4e1a2eba2b62ca422289e7cc19d7bbc156c9293957567'
assert ''.join(difflib.unified_diff(baseline.read_text().splitlines(True), candidate.read_text().splitlines(True), fromfile=str(baseline), tofile='fresh-guard-after-immutable-alias-manifest')) == (S/'guard.patch').read_text()
def bodies(p):
    return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(p.read_text()).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
old = bodies(baseline); new = bodies(candidate)
assert {k for k in old if old[k] != new.get(k)} == {'directory_snapshot','fixed_check','bytes_in'}
assert set(new)-set(old) == {'preserved_alias_root'}
def without_alias_additions(p):
    out = []
    for n in ast.parse(p.read_text()).body:
        if isinstance(n,ast.FunctionDef) and n.name in {'preserved_alias_root','directory_snapshot','fixed_check','bytes_in'}: continue
        if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id.startswith('_ALIAS_') for x in n.targets): continue
        out.append(ast.dump(n,include_attributes=False))
    return out
assert without_alias_additions(baseline) == without_alias_additions(candidate)
fixture_manifest = S/'fixture-identities03.json'
assert pin(fixture_manifest) == dict(path=str(fixture_manifest), bytes=32230, sha256='23407ab140c3b0b23af3d5d6f4fb452b7b739488580927b3984321e4f86b67eb')
fixture = strict(fixture_manifest.read_bytes())
assert set(fixture) == {'root','files','links'} and fixture['root'] == str(S/'DATA02')
assert len(fixture['files']) == 85 and len(fixture['links']) == 3
actual_files = {str(p) for p in (S/'DATA02').rglob('*') if p.is_file() and not p.is_symlink()}
actual_links = {str(p):os.readlink(p) for p in (S/'DATA02').rglob('*') if p.is_symlink()}
assert actual_files == set(fixture['files']) and actual_links == fixture['links']
for path, item in fixture['files'].items(): assert pin(Path(path)) == item
assert all(Path(target).is_relative_to(S/'DATA02') for target in fixture['links'].values())
fixture_code = '''def storage_fixture_aliases(config):
    identity=IDENTITY
    require(config['static_records'].get(identity['path'])==identity,'exact alias DATA fixture manifest')
    value=strict_json(read_pin(identity));require(set(value)=={'root','files','links'} and value['root']==ROOT,'closed isolated fixture root')
    require(set(phase_files(value['root']))==set(value['files'])|set(value['links']),'closed isolated DATA fixture physical keyset')
    for path,item in value['files'].items():
        require(config['static_records'].get(path)==item,'exact fixture input pin');checked_pin(item)
    for path,target in value['links'].items():require(path.startswith(value['root']+'/')and directory_link(path)==target,'exact isolated DATA link')
    return {path:{'path':target}for path,target in value['links'].items()}
'''.replace('IDENTITY', repr(pin(fixture_manifest))).replace('ROOT', repr(str(S/'DATA02')))
deployed_tree = ast.parse(deployed.read_text())
extra = next(n for n in deployed_tree.body if isinstance(n,ast.FunctionDef) and n.name == 'storage_fixture_aliases')
assert ast.dump(extra,include_attributes=False) == ast.dump(ast.parse(fixture_code).body[0],include_attributes=False)
expected = candidate.read_text().replace('_ALIAS_MANIFEST_PIN=None', '_ALIAS_MANIFEST_PIN='+repr(pin(manifest)))
needle = '**data_fixture_aliases(config),**directory_fixture_aliases(config)}'
assert expected.count(needle) == 1
expected = expected.replace(needle, '**data_fixture_aliases(config),**directory_fixture_aliases(config),**storage_fixture_aliases(config)}')
assert [ast.dump(n,include_attributes=False) for n in ast.parse(expected).body] == [ast.dump(n,include_attributes=False) for n in deployed_tree.body if n is not extra]
assert "if name in preserved_alias_root(parent):continue" in candidate.read_text()
assert "archived input alias reappeared" in candidate.read_text() and "qualified companion absence" in candidate.read_text()

data = strict((S/'DATA02/results01.json').read_bytes())
assert data['all_passed'] and data['total'] == len(data['cases']) == 18 and data['candidate'] == pin(candidate)
inventory = strict((S/'DATA02/inventory01.json').read_bytes())
for relative, identity in inventory.items():
    p = S/'DATA02'/relative
    assert p.is_relative_to(S/'DATA02') and p.is_file() and not p.is_symlink() and pin(p) == identity

# Repeat only isolated filesystem/AST-loop controls in Root-owned scratch.
# No Lean, guard main, dispatcher, or production input mutation is executed.
scratch = J/'alias-storage275-data-review299'
assert not scratch.exists()
scratch.mkdir()
(scratch/'guard-candidate.py').write_bytes(candidate.read_bytes())
controls = (S/'DATA02/controls.py').read_text()
needle = "S=Path("+repr(str(S))+");D=S/'DATA02'"
assert controls.count(needle) == 1
controls = controls.replace(needle, "S=Path("+repr(str(scratch))+");D=S/'DATA02'")
script = scratch/'controls.py'
script.write_text(controls)
result = subprocess.run(['python3','-I','-B','-S',str(script)], capture_output=True, text=True, timeout=60)
assert result.returncode == 0, result.stderr
rerun = strict((scratch/'DATA02/results01.json').read_bytes())
assert rerun['all_passed'] and rerun['total'] == 18 and rerun['cases'] == data['cases']

report = dict(status='PASSED', manifest=pin(manifest), source_helper=pin(S/'archive_aliases.py'), original_control_script=pin(S/'DATA02/controls.py'), original_results=pin(S/'DATA02/results01.json'), independent_data_results=pin(scratch/'DATA02/results01.json'), baseline_guard=pin(baseline), candidate_guard=pin(candidate), deployed_guard=pin(deployed), roots=266, preserved_links=links, original_metadata_bytes=total, archive_bytes=packed, unique_regular_targets=len(targets), complete_original_overlay_keysets_exact=True, all_archived_paths_honestly_absent=True, all_regular_targets_exact=True, original_controls=18, independent_controls=18, scope='Only structural recovery of obsolete OWNED imported-input symlink names/targets/mode/mtime/size, preserving every original overlay mapping and exact current regular target object. Current unlisted roots remain physical, archived-path reappearance is rejected even when warm, absent optional companions are now explicitly enforced. No arbitrary source/object/receipt fallback; no additional proof qualification or physical artifact charge for honestly absent historical links. All other guard AST including physical verifier/heap/RSS/RAM/disk/time/thread/cleanup/admission rules unchanged. Immutable completed manifest pin only, never a config override. Root bounded lossless data verification and isolated filesystem/AST-loop controls only; no guard main/dispatcher/Lean execution.', full_transfer='OPEN')
out = J/'mac-inactive-alias-preservation-review299.json'
assert not out.exists()
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','roots','preserved_links','unique_regular_targets','independent_controls']}))
