"""Review exact historical guard deltas without changing producer code."""
from pathlib import Path
import hashlib,json,difflib
J=Path(__file__).parent;W=J.parent.parent;G=W/'shared-build-handoff'
stages=['mac-full-arithmetic45-source01','mac-full-arithmetic45-execution03','mac-full-arithmetic45-execution04','mac-full-arithmetic45-execution05','mac-full-arithmetic45-execution08','mac-full-arithmetic45-execution11','mac-full-arithmetic45-execution12','mac-full-arithmetic45-execution19'];scripts=[(W/n/'maintained/guard.py').read_text()for n in stages]
a,b=scripts[:2];expected=a.replace("for spec in config['modules'].values(): source_check(read_pin(spec['source']),spec)","for spec in config['modules'].values(): checked_pin(spec['source'])\n    spec=config['modules'][config['_active_module']]\n    source_check(read_pin(spec['source']),spec)").replace("name=args.module; require(name in config['order'] and admission['module']==name, 'exact name admission')","name=args.module; require(name in config['order'] and admission['module']==name, 'exact name admission')\n    config['_active_module']=name");assert expected==b
assert scripts[3]==scripts[2].replace('metadata<=32*1024*1024','metadata<=128*1024*1024').replace("['metadata_bytes']<=27*1024*1024","['metadata_bytes']<=124*1024*1024")
assert scripts[4]==scripts[3].replace('fixed_check(config,records); cancelled();pre=bounds(config);launch_reserve(pre)','cancelled();pre=bounds(config);launch_reserve(pre)').replace('fixed_check(config,records);cancelled();pre=bounds(config);launch_reserve(pre)','cancelled();pre=bounds(config);launch_reserve(pre)')
assert 'fixed_check(config,records) # actual PACKAGE lookup after layout exists, under held lock'in scripts[4]
assert scripts[6]==scripts[5].replace('metadata<=128*1024*1024','metadata<=256*1024*1024').replace("['metadata_bytes']<=124*1024*1024","['metadata_bytes']<=252*1024*1024")
assert scripts[7]==scripts[6].replace('metadata<=256*1024*1024','metadata<=512*1024*1024').replace("['metadata_bytes']<=252*1024*1024","['metadata_bytes']<=508*1024*1024")
records=[]
for i,(stage,script)in enumerate(zip(stages,scripts)):
 records.append(dict(stage=stage,bytes=len(script.encode()),sha256=hashlib.sha256(script.encode()).hexdigest(),delta_from_previous=None if i==0 else '\n'.join(difflib.unified_diff(scripts[i-1].splitlines(),script.splitlines(),fromfile=stages[i-1],tofile=stage,n=3))))
for script in scripts:
 assert "elapsed<=240"in script and 'rss<=4*1024*1024*1024'in script and 'disk>=2*1024*1024*1024 and memory>=15'in script
 assert "'-j1','-M2048'"in script and "LEAN_NUM_THREADS"in script and 'fcntl.LOCK_EX|fcntl.LOCK_NB'in script and 'one heavy physical-host lane'in script
 assert 'fixed_check(config,records) # actual PACKAGE lookup after layout exists, under held lock'in script
out=dict(kind='Historical exact guard/source delta review; no compiler or mutation',guards=records,semantic_changes='Active module source parsing only while hashing all sources; pure import-header memoization keyed by exact byte digest; redundant pre-layout check removal retaining the held-lock actual PACKAGE check; canonical per-module source-root validation and matching -R; finite on-disk metadata thresholds',physical_changes=False,source_identity_checks_preserved=True,import_header_memoization='Execution03to04 reviewed source: unchanged parsing plus per-process exact-digest memoization',physical='One thread/M2048/4GiBownedRSS/240sec/15percentfreeRAM/2GiBdisk/oneheldheavy-hostlock, unchanged',full_transfer='OPEN')
(J/'guard-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(guards=len(records),physical_changes=False)))
