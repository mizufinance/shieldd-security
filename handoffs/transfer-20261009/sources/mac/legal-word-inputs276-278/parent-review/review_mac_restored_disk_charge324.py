from pathlib import Path
import ast,hashlib,json,copy
J=Path(__file__).parent;W=J.parent;old=W/'mac-full-arithmetic45-execution307/maintained/guard.py';new=W/'mac-full-arithmetic45-execution308/maintained/guard.py'
pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
assert pin(old)['sha256']=='40dadbd3499694382bb3b9477c0ad99ecfa980b91c036d41da34ab42776e7022';assert pin(new)['sha256']=='59992e67fcf97456530454e56b07b18a4d6b11eb4580720283626f360bc16d99'
prior=J/'mac-official-restoration-review323.json';assert json.loads(prior.read_text())['status']=='PASSED'
a=ast.parse(old.read_text());b=ast.parse(new.read_text());f=next(n for n in b.body if isinstance(n,ast.FunctionDef)and n.name=='restored_official_charge');b.body.remove(f)
bounds=next(n for n in b.body if isinstance(n,ast.FunctionDef)and n.name=='bounds');changes=[n for n in bounds.body if isinstance(n,ast.Assign)and 'restored_official_charge(config)'in ast.unparse(n)]+[n for n in bounds.body if isinstance(n,ast.AugAssign)and ast.unparse(n)in ['total += restored_bytes','metadata += restored_metadata']];assert len(changes)==3
for n in changes:bounds.body.remove(n)
cap=next(n for n in bounds.body if ast.unparse(n).startswith('require(total <= 4 *'));replacement=ast.parse("require(total<=2*1024*1024*1024 and metadata<=1024*1024*1024, 'batch disk/metadata cap')").body[0];bounds.body[bounds.body.index(cap)]=replacement
launch=next(n for n in b.body if isinstance(n,ast.FunctionDef)and n.name=='launch_reserve');assert len(launch.body)==2;launch.body[1]=ast.parse("require(observation['batch_bytes']<=2032*1024*1024, 'reserve new object/streams/receipt')").body[0]
assert ast.dump(a,include_attributes=False)==ast.dump(b,include_attributes=False)
g={'__name__':'SOURCE_DATA_ONLY','__file__':str(new)};exec(compile(new.read_bytes(),str(new),'exec'),g)
cfgpath=new.parent.parent/'config01.json';config=g['read_config'](str(cfgpath),pin(cfgpath)['sha256']);total,metadata=g['restored_official_charge'](config);assert total==417098969
actual=json.loads((W/'mac-official-cache277-restoration03/result01.json').read_bytes());assert metadata==sum(v['bytes']for r in actual['records']for p,v in r['objects'].items()if p.endswith('.ilean'));g['checked_phase_close']()
bad=copy.deepcopy(config);bad['static_records'].pop(str(W/'mac-official-cache277-restoration03/result01.json'))
try:g['restored_official_charge'](bad);raise AssertionError('unbound restoration accepted')
except RuntimeError as e:assert str(e)=='fixed exact restoration result'
bad=copy.deepcopy(config);first=next(iter(actual['records'][0]['objects']));bad['charged_roots'].append(str(Path(first).parent))
try:g['restored_official_charge'](bad);raise AssertionError('overlapping charge accepted')
except RuntimeError as e:assert str(e)=='unique newly restored output charge'
report=dict(status='PASSED',baseline_guard=pin(old),successor_guard=pin(new),restoration_review=pin(prior),charged_restored_bytes=total,charged_ilean_bytes=metadata,controls=['actual fixed result all objects charged and pinned; terminal checks passed','missing static result pin refused','overlapping charged root refused'],scope='Only AST delta: exact fixed627-module2508-object restoration charge; task-owned artifact packaging cap2GiB→4GiB and corresponding16MiB reserve2032→4080MiB. This is a finite disk accounting allowance, not a free-disk/heap/RSS/RAM/process/time relaxation. Free-disk admission2GiB, RAM15%, metadata1GiB and all physical verifier constraints retain identical AST. Every new cache object charged once, all physical bytes checked, overlap refused. Isolated actual charge helper only, no production bounds/main/dispatcher/Lean or new proof qualification.',full_transfer='OPEN')
out=J/'mac-restored-disk-charge-review324.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print('PASSED exact restoration charge; packaging4GiB/freefloor2GiB; physical verifier checks unchanged')
