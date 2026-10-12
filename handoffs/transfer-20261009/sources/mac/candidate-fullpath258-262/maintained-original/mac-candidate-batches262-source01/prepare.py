from pathlib import Path
import json,hashlib,sys,re,runpy,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution285';OLD=W/'mac-prefix-candidate258-source02';S=W/'mac-candidate-batches262-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'immutable batch source');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);events=[json.loads(x)for x in(P/'runtime/ledger.jsonl').read_bytes().splitlines()];require(len(events)==38 and events[-1]['kind']=='result','balanced stopped285');passed=set(c['qualified_batch_imports']);receiptPins=[]
for e in events:
 if e['kind']=='result':r=json.loads(Path(e['receipt']['path']).read_bytes());require(r['status']=='passed' and r['cleanup']['clean'] and r['cleanup']['leader_reaped'],'preserved pass');passed.add(r['module']);receiptPins.append(e['receipt'])
old=json.loads((OLD/'templates01.json').read_bytes());pending=[n for n in old['modules']if n not in passed];require(pending==['CandidateRows258P'+str(i).zfill(3)for i in range(37,232)],'exact195 unqualified original proof bodies');pre='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n';mods={};bindings={};inputs={str(OLD/'templates01.json'):pin(OLD/'templates01.json'),str(OLD/'generation01.json'):pin(OLD/'generation01.json'),str(P/'runtime/ledger.jsonl'):pin(P/'runtime/ledger.jsonl')}
for p in receiptPins:inputs[p['path']]=p
for i in range(0,len(pending),16):
 members=pending[i:i+16];name='CandidateBatch262B'+str(i//16).zfill(2);imports=[];bodies=[];audits=[]
 for n in members:
  d=old['modules'][n];body=d['body'];marker='namespace ShielddSecurity.'+n+'\n';require(body.count(marker)==1 and d['names']==['rows'],'one exact original theorem');before,inside=body.split(marker);require(before.endswith(pre),'exact finite preamble');imports+=re.findall(r'^import ([\w.]+)\s*$',before,re.M);bodies.append(marker+inside);audits.append(n+'.rows');source=OLD/'source-root/ShielddSecurity'/(n+'.lean');inputs[str(source)]=pin(source);bindings[n]=dict(physical_module=name,original_source=pin(source),qualified_audit='ShielddSecurity.'+n+'.rows',proof_body_sha256=hashlib.sha256((marker+inside).encode()).hexdigest())
 imports=list(dict.fromkeys(imports));mods[name]=dict(body=''.join('import '+n+'\n'for n in imports)+pre+''.join(bodies),names=audits,qualified_audits=True,members=members)
for n in passed:
 if n in old['modules']:bindings[n]=dict(physical_module=n,previously_passed=True)
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source disk floor');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());gen=(W/'mac-merkle-sparse243-source02/generate.py').read_text();gen=gen.replace("names=['ShielddSecurity.'+module+'.'+n for n in d['names']]","names=['ShielddSecurity.'+(n if d.get('qualified_audits') else module+'.'+n) for n in d['names']]");(S/'generate.py').write_text(gen);put('namespace-map01.json',dict(bindings=bindings,original_names=list(old['modules']),scope='195 unchanged original theorem bodies grouped in13 physical modules;37 accepted predecessors reused without compilation. No alias objects or namespace-import fallback.'))
put('templates01.json',dict(modules=mods,inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',modules=len(mods),reports=195,body_preservation='Original namespace/open/variable/theorem/proof bytes EXACT; only repeated identical finite preambles and import headers deduplicated by maintained producer',open=['Every new batch module/audit UNRUN','Symbolic collectors/path/remaining all-assertion/legal/native/full Transfer'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
print(json.dumps(dict(stage=str(S),modules=len(mods),reports=195)))
