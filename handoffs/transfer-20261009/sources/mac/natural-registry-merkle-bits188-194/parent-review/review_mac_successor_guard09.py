"""Review exact sealed runner delta and pure physical expressions; no verifier launch."""
from pathlib import Path
from types import SimpleNamespace
import ast,difflib,hashlib,json
J=Path(__file__).parent;W=J.parent
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
old=W/'mac-full-arithmetic45-execution205/maintained/guard.py';fresh=W/'mac-full-arithmetic45-execution206/maintained/guard.py'
assert pin(old)['sha256']=='8843eb3854ca31545517a327c39fe7f185f0097b95fe21d3a0fa78351c3b1b30'
assert pin(fresh)['sha256']=='2245839157e8064968f67c2f9e69976b06837b0760f4fce9bc0b7832a060b792'
before=old.read_text();after=fresh.read_text();expected=before
changes=[
 ("for alias in config['alias_records']: read_pin(alias)","for alias in config['alias_records']: checked_pin(alias)"),
 ("require(config['carried_attempts']+len(events)//2<=config['limits']['total_attempts'] and config['carried_lean_seconds']+sum(x['lean_seconds'] for x in records)<=config['limits']['aggregate_lean_seconds'], 'cumulative pacing including protected consumption')","require(len(events)//2<=len(config['order']) and all(type(x['lean_seconds']) in (int,float) and 0<=x['lean_seconds']<=240 for x in records), 'finite individually qualified named-job accounting')"),
 ("require(name==config['order'][len(records)] and len(records)+config['carried_attempts']<config['limits']['total_attempts'], 'next named module and remaining attempts')","require(name==config['order'][len(records)], 'next exact named module; no replay')"),
 ("require(elapsed<=240 and consumed+elapsed<=config['limits']['aggregate_lean_seconds'], 'module/aggregate seconds')","require(elapsed<=240, 'module seconds')"),
 ("observation=bounds(config);observations.append({'seconds':elapsed,'rss':rss,**observation});last_resource=elapsed","diskstat=os.statvfs(config['batch_root']);diskfree=diskstat.f_bavail*diskstat.f_frsize;memoryfree=free_memory();require(diskfree>=2*1024*1024*1024 and memoryfree>=15, 'live RAM/disk physical floor');observations.append({'seconds':elapsed,'rss':rss,'free_memory_percent':memoryfree,'free_disk_bytes':diskfree,'scope':'live physical RAM/disk; complete artifact census retained pre/post'});last_resource=elapsed"),
 ("require(elapsed<=240 and config['carried_lean_seconds']+sum(r['lean_seconds'] for r in records)+elapsed<=config['limits']['aggregate_lean_seconds'], 'post-run aggregate seconds including retained failure')","require(elapsed<=240, 'post-run module seconds including cleanup')")]
for a,b in changes:assert expected.count(a)==1;expected=expected.replace(a,b)
assert expected==after
for n in [207,208]:assert (W/f'mac-full-arithmetic45-execution{n}/maintained/guard.py').read_bytes()==fresh.read_bytes()
physical=dict(threads=1,heap_MiB=2048,group_rss_bytes=4294967296,module_seconds=240,minimum_free_RAM_percent=15,minimum_free_disk_bytes=2147483648,heartbeats=900000,recdepth=8192)
configs=[]
for n in [206,207,208]:
 p=W/f'mac-full-arithmetic45-execution{n}/config01.json';c=json.loads(p.read_bytes())
 assert all(c['limits'][k]==v for k,v in physical.items()) and c['lean_environment']['LEAN_NUM_THREADS']=='1'
 assert 'total_attempts'not in c['limits']and 'aggregate_lean_seconds'not in c['limits']
 assert c['carried_attempts']>0 and c['carried_lean_seconds']>0 and c['carried_failure']
 configs.append(pin(p))
assert "cancelled();pre=bounds(config);launch_reserve(pre)"in after and "post=bounds(config)"in after
assert "require(not any(pathlib.Path(p['comm']).name in {'lean','lake','cargo','rustc'}"in after
assert "_CHECKED.clear()"in after and "rss<=4*1024*1024*1024"in after
# Run the actual new expression with in-memory synthetic physical observations only.
line=next(l.strip()for l in after.splitlines()if l.strip().startswith('diskstat=os.statvfs'))
account=ast.parse(after);expr=next(n.args[0]for n in ast.walk(account)if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='require'and len(n.args)>1 and isinstance(n.args[1],ast.Constant)and n.args[1].value=='finite individually qualified named-job accounting')
def require(ok,message):
 if not ok:raise RuntimeError(message)
observations=[]
for disk,mem,accept in [(2147483648,15,True),(2147483647,15,False),(2147483648,14,False),(2147483649,16,True)]:
 env=dict(os=SimpleNamespace(statvfs=lambda _:SimpleNamespace(f_bavail=disk,f_frsize=1)),config={'batch_root':'mock'},free_memory=lambda:mem,require=require,observations=[],elapsed=1,rss=1)
 try:exec(line,env);ok=True
 except RuntimeError:ok=False
 assert ok==accept;observations.append(dict(disk=disk,memory=mem,accepted=ok))
for value,accept in [(240,True),(240.1,False),(-1,False),(True,False),(float('nan'),False)]:
 env=dict(events=[{},{}],config={'order':['one']},records=[{'lean_seconds':value}]);ok=eval(compile(ast.Expression(expr),str(fresh),'eval'),env);assert ok==accept
diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile=str(old),tofile=str(fresh)));(J/'mac-successor-guard-delta206.diff').write_text(diff)
report=dict(status='PASSED',kind='Exact runner source/config and mock expression review; no Lean/native/process launch',guard=pin(fresh),same_guards=[207,208],configuration_pins=configs,physical_limits=physical,scope='Administrative cumulative stop quotas removed as authorized; finite named jobs, full historical costs/failures and exact one-claim/no-replay remain. Live polling checks physical RAM/disk while full artifact census remains pre/post. Alias identity cache clears each fixed-check phase and byte-consuming reads remain unchanged.',pure_expression_observations=observations,all_other_guard_source_exact=True,full_transfer='OPEN')
(J/'mac-successor-guard-review09.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',guard=report['guard'],physical_limits=physical)))
