"""Independent source delta and isolated cold/warm history controls; no verifier."""
from pathlib import Path
import ast,hashlib,json,os,tempfile,subprocess,datetime
J=Path(__file__).resolve().parent;W=J.parent;old=W/'mac-full-arithmetic45-execution271/maintained/guard.py';S=W/'mac-carried-proof-cache249-source01';new=S/'guard.py';deployed=W/'mac-full-arithmetic45-execution272/maintained/guard.py'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
assert pin(old)['sha256']=='2851e1c826d82a1e37784ece5e19a903680bf59d4b9db98448828b7b01f72807'
assert pin(new)['sha256']=='e1e43ace6927b7e3fe3904c69322be5fd6f62fcfe8839c5e75b97f418a394fa9'and new.read_bytes()==deployed.read_bytes()
def functions(p):return {n.name:n for n in ast.parse(p.read_text()).body if isinstance(n,ast.FunctionDef)}
a,b=functions(old),functions(new);assert set(b)==set(a)|{'_carried_check_cold'}
assert [k for k in a if ast.dump(a[k])!=ast.dump(b[k])]==['carried_check']
cold=new.read_text()[new.read_text().index('def _carried_check_cold'):new.read_text().index('# Historical audit/keyset')]
expected=old.read_text()[old.read_text().index('def carried_check'):old.read_text().index('def overlay_map')].replace('def carried_check','def _carried_check_cold')
needle="            require(audit_log(read_pin(r['stdout']),[a['name'] for a in r['audits']])==r['audits'],'previous exact type/axiom audits')"
expected=expected.replace(needle,needle+"\n            checked_pin(r['stdout']) # register initial exact parsed-byte identity for every terminal check")
assert cold==expected
def unchanged_nodes(p):
 return [ast.dump(n)for n in ast.parse(p.read_text()).body if not isinstance(n,ast.FunctionDef)and not(isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id.startswith('_CARRIED_PROOF')for t in n.targets))]
assert unchanged_nodes(old)==unchanged_nodes(new)
for rel,v in json.loads((S/'producer-manifest01.json').read_text()).items():
 p=S/rel
 if 'symlink_target'in v:assert p.is_symlink()and os.readlink(p)==v['symlink_target']and pin(p.resolve())==v['target']
 else:assert pin(p)==v
original=json.loads((S/'controls01.json').read_text());assert len(original['cases'])==11
with tempfile.TemporaryDirectory(prefix='root-carried-guard28-',dir=J)as tmp:
 T=Path(tmp)/'source';prepare=Path(tmp)/'prepare.py'
 text=(S/'prepare.py').read_text().replace("S=W/'mac-carried-proof-cache249-source01'","S=Path("+repr(str(T))+")")
 assert text!=(S/'prepare.py').read_text()
 prepare.write_text(text)
 result=subprocess.run(['python3','-I','-B','-S',str(prepare)],capture_output=True,text=True,timeout=45)
 assert result.returncode==0,result.stderr
 assert(T/'guard.py').read_bytes()==new.read_bytes()
 controls=json.loads((T/'controls01.json').read_text())['cases'];assert len(controls)==11
 assert controls[0]['actual_audit_calls']==1 and controls[0]['cache_bytes']<32*1024*1024
 assert all('refused'in x for x in controls[1:])
 controls=[{**x,'refused':x.get('refused','').replace(str(T),'ROOT_TEMP')}for x in controls]
r=dict(status='PASSED',kind='Independent exact AST/body source delta and isolated cold/warm production primitive controls; no Lean or guard execute',old=pin(old),successor=pin(new),deployed=pin(deployed),source=pin(S/'prepare.py'),original_controls=pin(S/'controls01.json'),root_controls=controls,physical_limits='UNCHANGED; every prelaunch/resource/cleanup/source/object/load/directory/file/archive/absence check AST-identical. Only historical audit parsing/keyset validation memoized within one dispatcher, keyed by exact history pin/counters/repair additions. Eight contexts/32MiB cap.',scope='Initial cold check remains exact old verification plus stdout identity registration; immutable directory tokens rechecked on every warm hit, all registered file/archive and original-absence identities checked by unchanged terminal closure immediately before Popen and acceptance. No raw object/log contents cached and no cross-process memo. Previous archive absence controls26 still apply via AST-identical primitives.',full_transfer='OPEN',root_verifier_execution='NONE',time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(J/'mac-carried-history-cache-guard-review28.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',root_controls=len(controls),guard=r['successor']['sha256'],physical_limits='UNCHANGED')))

