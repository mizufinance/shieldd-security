"""Review immutable archival-map successors and guard-only constant deltas."""
from pathlib import Path
import ast, hashlib, json, lzma, difflib, importlib.util
J=Path(__file__).parent; W=J.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
baseline=W/'mac-history-metadata-preservation126-15/archive-map01.json'
assert sha(baseline.read_bytes())=='27c9f9a30f9420ac64033631f626d9087c063ddf943692c18bfe0577f75ac69d'
previous=json.loads(baseline.read_bytes()); added=[]
for number,digest in [(16,'e6b0b4373e77e3ee590edde7f245d952903f93c80ffe9a2475b1a101ffdbd722'),(17,'3db1917c8bd706c04f0cfa929cbe97f5c46237ba28229c524e89677c872476b6')]:
 p=W/f'mac-history-metadata-preservation126-{number}/archive-map01.json';raw=p.read_bytes();assert sha(raw)==digest
 current=json.loads(raw);assert current['schema']==previous['schema']=='exact-inactive-configuration-storage01'
 assert all(current['records'][k]==v for k,v in previous['records'].items())
 for k,r in current['records'].items():
  if k in previous['records']:continue
  original=r['original'];q=Path(r['archive']['path']);source=Path(k)
  assert source.parent.parent==W and source.name=='config01.json' and source.parent.name.removeprefix('mac-full-arithmetic45-execution').isdigit()
  assert original['path']==k and 0<original['bytes']<=16*1024*1024
  assert q.is_file() and not q.is_symlink() and q.parent==p.parent and q.suffix=='.xz'
  b=q.read_bytes();assert len(b)==r['archive']['bytes'] and sha(b)==r['archive']['sha256']
  decoder=lzma.LZMADecompressor(memlimit=128*1024*1024);data=decoder.decompress(b,max_length=original['bytes']+1)
  assert decoder.eof and not decoder.unused_data and len(data)==original['bytes'] and sha(data)==original['sha256'];json.loads(data)
  if source.exists():assert source.read_bytes()==data
  added.append(r)
 previous=current
reader=(J/'read_preserved_mac_config05.py').read_text().replace('preservation126-15','preservation126-17').replace('27c9f9a30f9420ac64033631f626d9087c063ddf943692c18bfe0577f75ac69d','3db1917c8bd706c04f0cfa929cbe97f5c46237ba28229c524e89677c872476b6').replace('len(raw) == 106543','len(raw) == 108391')
(J/'read_preserved_mac_config06.py').write_text(reader)
spec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config06.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
strip=lambda t:ast.dump(ast.Module(body=[n for n in t.body if not(isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='_STORAGE_PIN' for x in n.targets))],type_ignores=[]),include_attributes=False)
guards=[];prior=W/'mac-full-arithmetic45-execution186/maintained/guard.py';assert sha(prior.read_bytes())=='6217fe1842defd749fbe03e34a46024234156c16f2a36a15ca58824b845c218c'
physical={'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
for stage,digest in [(187,'6136469756b71f179b33ac2e4f82ffa2c76eec63855c54aecea559201be9fbe3'),(188,'ff6c299719ba874c19deba3f335e834c1d30a98bf57cad0840ddd96b9ec36a70'),(190,'8a721a59a67eb2bf089ead277561be83a41be8557d61735c9fd8e3328cfc39ce'),(195,'c4ad8921031707767f33c5445f0eb772a844e8690c511361104db31c0b04ef40')]:
 p=W/f'mac-full-arithmetic45-execution{stage}/maintained/guard.py';b=p.read_bytes();assert sha(b)==digest
 expected=prior.read_text()
 if stage==188:
  before="        require(actual==set(h['entries']), 'protected history closed physical+exact-archived file/link keyset')\n        for identity in h['entries'].values():"
  after="""        expected=dict(h['entries'])
        additions=config['history_closed_keyset_additions']
        require(set(additions)=={'/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-full-arithmetic45-execution186/config01.json'}, 'exact single archived-keyset repair')
        for key,identity in additions.items():
            require(preserved_configs()[key]['original']==identity, 'exact archived original addition')
            if any(pathlib.Path(key).is_relative_to(pathlib.Path(root)) for root in h['roots']) and key not in expected:
                checked_pin(identity);expected[key]=identity
        require(actual==set(expected), 'protected history closed physical+exact-archived file/link keyset')
        for identity in expected.values():"""
  assert expected.count(before)==1;expected=expected.replace(before,after)
 if stage==195:
  assert expected.count('_CHECKED = {}\n')==1;expected=expected.replace('_CHECKED = {}\n','_CHECKED = {}\n_ARCHIVE_PROOFS = set()\n')
  before='            read_pin(identity)\n            after=archive.stat()'
  after="""            # Every phase rehashes the exact compressed archive. A successful
            # prior bounded decode binds the original SHA to these same bytes.
            checked_pin(record['archive'])
            proof=(str(path),identity['bytes'],identity['sha256'],record['archive']['path'],record['archive']['bytes'],record['archive']['sha256'])
            if proof not in _ARCHIVE_PROOFS:
                read_pin(identity)
                _ARCHIVE_PROOFS.add(proof)
            after=archive.stat()"""
  assert expected.count(before)==1;expected=expected.replace(before,after)
 a,t=ast.parse(expected),ast.parse(b);assert strip(a)==strip(t)

 pins=[ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='_STORAGE_PIN' for x in n.targets)];assert len(pins)==1
 pin=pins[0];data=Path(pin['path']).read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
 config=json.loads(preserved.read_config(p.parent.parent/'config01.json'))
 if stage>=188:
  extra=config['history_closed_keyset_additions'];key=str(W/'mac-full-arithmetic45-execution186/config01.json');assert set(extra)=={key} and extra[key]==previous['records'][key]['original']
 assert all(config['limits'][k]==v for k,v in physical.items()) and config['lean_environment']['LEAN_NUM_THREADS']=='1'
 guards.append({'guard':{'path':str(p),'bytes':len(b),'sha256':digest},'baseline_sha256':sha(prior.read_bytes()),'storage_map':pin,'only_storage_constant_changed':stage in [187,190], 'precisely_reviewed_extra_delta':{188:'Exact single archived execution186 original config identity added to closed historical keyset; all original expected entries retained and exact equality checked',195:'Memoizes one successful bounded original decode keyed by full original/archive identity; compressed archive is rehashed in every phase, original caller read_pin decoding unchanged'}.get(stage)})
 (J/f'pending-mac-archived-metadata-guard-delta{stage}.diff').write_text(''.join(difflib.unified_diff(prior.read_text().splitlines(True),p.read_text().splitlines(True),fromfile=str(prior),tofile=str(p))))
 prior=p
out={'status':'PASSED','scope':'Source/metadata review only; no verifier launch','guards':guards,'physical_limits':physical,'latest_map_records':len(previous['records']),'prior173_records_unchanged':True,'new_original_records':added,'new_original_bytes':sum(r['original']['bytes']for r in added),'review':'Guard successors differ only by immutable map constants, precise execution186 original config closed-keyset addition, and original/archive exact-identity decode memoization with compressed archive rehashed per phase. Every other AST statement, including launch/monitor/physical/time/cleanup protections, is unchanged. Old173 records unchanged and every additional original config reproduced under bounded identity/EOF checks. No source or proof byte changed.','full_transfer':'OPEN'}
(J/'mac-archived-metadata-successors-review05.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['status','latest_map_records','new_original_bytes']}))
