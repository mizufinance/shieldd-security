from pathlib import Path
import json,hashlib,lzma,os,re,ast,sys,copy
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';P=W/'mac-full-arithmetic45-execution233';S=W/'mac-full-arithmetic45-execution234';storage=W/'mac-history-metadata-preservation126-35'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(p):
 p=Path(p)
 if p.exists():return p.read_bytes()
 table=json.loads((storage/'archive-map01.json').read_bytes())['records'];record=table[str(p)];require(pin(record['archive']['path'])==record['archive'],'exact archive');decoder=lzma.LZMADecompressor();raw=decoder.decompress(Path(record['archive']['path']).read_bytes(),max_length=record['original']['bytes']+1);require(decoder.eof and not decoder.unused_data and len(raw)==record['original']['bytes']and hashlib.sha256(raw).hexdigest()==record['original']['sha256'],'exact bounded preserved original');return raw
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation')
wrapped=json.loads(read(P/'config01.json'));require(wrapped['schema']=='bounded-pinned-execution-delta01','exact prior config schema');base=json.loads(read(wrapped['base']['path']));prior=copy.deepcopy(base);prior.update(wrapped['replace']);
for k,v in wrapped['merge'].items():prior[k].update(v)
require(hashlib.sha256((json.dumps(prior,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()==wrapped['effective_sha256'],'prior effective config');c=copy.deepcopy(prior);history=json.loads(read(c['carried_failure']['path']));raw=(P/'runtime/ledger.jsonl').read_bytes();events=[json.loads(x)for x in raw.splitlines()];require(raw.endswith(b'\n')and len(events)==2 and events[-1]['kind']=='result','exact terminal228 checkpoint');rps=[x['receipt']for x in events if x['kind']=='result'];current=[json.loads(Path(p['path']).read_bytes())for p in rps];require([r['status']for r in current]==['failed']and current[-1]['error']=="RuntimeError('diagnostic refusal')",'exact resource refusal; no elaboration retry');require(all(r['cleanup']['clean']and r['cleanup']['leader_reaped']for r in current),'owned cleanup');receipts=history['receipts']+rps;rs=[json.loads(Path(p['path']).read_bytes())for p in receipts];require(len(rs)==1233 and sum(r['status']=='failed'for r in rs)==128,'all consumed history');require(not S.exists(),'fresh successor');S.mkdir();entries={};links={}
partials=[]
for p in [p for root in[P,*partials]for p in root.rglob('*')]:
 if p.is_symlink():v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
for key,v in json.loads((storage/'archive-map01.json').read_bytes())['records'].items():
 if any(key.startswith(str(root)+'/')for root in[P,*partials]):entries[key]=v['original']
put('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(root)for root in[P,*partials]],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(rps,current):
 if r['status']!='passed':continue
 n=r['module'];cache=Path(r['command'][r['command'].index('-o')+1]).parent;c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
old=(P/'maintained/guard.py').read_bytes();require(hashlib.sha256(old).hexdigest()=='4246526db55be02599bb06bdaf002e1b97800d8ae1c2d3487633fa4f8187d825','exact old guard');a=old.index(b'_STORAGE_PIN = ');b=old.index(b'\n_STORAGE =',a);old=old[:a]+b'_STORAGE_PIN = '+repr(pin(storage/'archive-map01.json')).encode()+old[b:]
ast.parse(old)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes(old);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());put('maintained-inventory01.json',{p.name:pin(p)for p in(S/'maintained').iterdir()})
for root in [*[W/('mac-history-metadata-preservation126-'+str(i))for i in[35]],W/'mac-captured-canonical217-source02',W/'mac-canonical-comparisons216-source01',W/'mac-canonical-comparisons216-data01']:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file():c['static_records'][str(p)]=pin(p)
newnames=[]
for root in [W/'mac-captured-canonical217-source02']:
 g=json.loads((root/'generation01.json').read_bytes())
 for o in g['outputs']:
  require(pin(o['source']['path'])==o['source'],'frozen generation');c['modules'][o['name']]=dict(source=o['source'],source_root=str(root/'source-root'),audits=o['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(o['source']['path']).read_text(),re.M));newnames.append(o['name'])
remaining=[n for n in c['order']if n not in c['qualified_batch_imports']and n not in newnames];order=[newnames[0]]+remaining
# Concrete canonical instances follow their original word-slot dependencies.
pos=order.index('CapturedWordRoot213')+1;order[pos:pos]=newnames[1:];require(len(order)==len(remaining)+len(newnames) and len(set(order))==len(order),'exact remaining topology')
available=set(c['qualified_batch_imports'])|set(json.loads(Path(c['closure']['path']).read_bytes())['modules'])
for n in order:
 for imp in c['modules'][n]['imports']:
  if imp.startswith('ShielddSecurity.'):require(imp.split('.',1)[1]in available,'dependency prior '+n+':'+imp)
 available.add(n)
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=order);c['charged_roots'].extend([str(S),*map(str,partials)]);c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
serial=(P/'dispatcher/serial.py').read_text();serial=serial.replace(";c=json.loads(config.read_bytes());mi=json.loads(inventory.read_bytes())",";mi=json.loads(inventory.read_bytes())");serial=serial.replace(" require(c['static_records'][str(Path(__file__))]==pin(Path(__file__)),'exact executing dispatcher')\n",'');serial=serial.replace(" g=runpy.run_path(str(guard),run_name='pinned_serial_guard')"," g=runpy.run_path(str(guard),run_name='pinned_serial_guard')\n c=g['read_config'](str(config),pin(config)['sha256']);require(c['static_records'][str(Path(__file__))]==pin(Path(__file__)),'exact executing dispatcher')");serial=serial.replace('current=json.loads(config.read_bytes())',"current=g['read_config'](str(config),pin(config)['sha256'])");ast.parse(serial);(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_text(serial)
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
put('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json')
replace={k:v for k,v in c.items()if k not in ['static_records','modules','qualified_batch_imports']and v!=base[k]};merge={k:{n:v for n,v in c[k].items()if n not in base[k]or v!=base[k][n]}for k in ['static_records','modules','qualified_batch_imports']};effective=(json.dumps(c,sort_keys=True,separators=(',',':'))+'\n').encode();basepin=wrapped['base'];put('config01.json',dict(schema='bounded-pinned-execution-delta01',base=basepin,replace=replace,merge=merge,effective_sha256=hashlib.sha256(effective).hexdigest(),effective_bytes=len(effective)))
ns={'__name__':'SOURCE_ONLY','__file__':str(S/'maintained/guard.py')};exec(compile(old,str(S/'maintained/guard.py'),'exec'),ns);loaded=ns['read_config'](str(S/'config01.json'),pin(S/'config01.json')['sha256']);require(loaded==c,'byte-equivalent reconstructed effective config');cases=[]
wrapper=json.loads((S/'config01.json').read_bytes())
# Pure DATA resolver mutation controls; no runtime/cache/intents/process startup.
for label,mutate in [('wrong-effective',lambda v:v.update(effective_sha256='0'*64)),('unknown-key',lambda v:v['replace'].update(unknown=True)),('overlap',lambda v:v['merge'].update(order={})),('wrong-base',lambda v:v['base'].update(sha256='0'*64)),('nested',lambda v:v['replace'].update(schema='x'))]:
 bad=copy.deepcopy(wrapper);mutate(bad);orig=ns['read_bound'];ns['read_bound']=lambda *a,**k:bad
 try:ns['read_config']('mock','mock');raise RuntimeError('mutation accepted '+label)
 except RuntimeError as e:require('mutation accepted'not in str(e),'expected refusal');cases.append(dict(case=label,refused=str(e)))
 finally:ns['read_bound']=orig
put('config-delta-DATA01.json',dict(scope='Pure in-memory config reconstruction; no guard execute/Popen/Lean/runtime/cache',effective_bytes=len(effective),effective_sha256=hashlib.sha256(effective).hexdigest(),positive_exact=True,negative=cases,old_guard=pin(P/'maintained/guard.py'),new_guard=pin(S/'maintained/guard.py')))
put('transition-observation01.json',dict(old_phase=str(P),ledger=pin(P/'runtime/ledger.jsonl'),failed=rps[-1],scope='1232 stopped on actual disk pressure, clean cleanup, no diagnostics. Six earlier passes inherited unchanged. Retry of B0068 requires fresh restored resource state. Exact old228 inputs archived losslessly in31; new config is bounded deterministic delta, no history reset.'))
put('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],remaining_named=len(order),new_names=newnames,guard=pin(S/'maintained/guard.py'),no_accepted_replay=True,scope='Autonomous actual canonical recovery + remaining Boolean/word/hash global obligations. Same per-run physical safeguards; no cumulative project quota.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),failures=128,first=order[:4],remaining=len(order),config=pin(S/'config01.json'),guard=pin(S/'maintained/guard.py'),producer=pin(S/'producer-manifest01.json'),physical=sum(p.stat().st_size for p in S.rglob('*')if p.is_file()))))
