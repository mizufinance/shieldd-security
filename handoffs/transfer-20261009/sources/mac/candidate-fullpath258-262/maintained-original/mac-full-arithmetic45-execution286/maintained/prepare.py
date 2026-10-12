from pathlib import Path
import json,hashlib,lzma,os,re,ast,sys,copy
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';P=W/'mac-full-arithmetic45-execution285';S=W/'mac-full-arithmetic45-execution286';storage=W/'mac-history-metadata-preservation126-37'
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
require(hashlib.sha256((json.dumps(prior,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()==wrapped['effective_sha256'],'prior effective config');c=copy.deepcopy(prior);history=json.loads(read(c['carried_failure']['path']));raw=(P/'runtime/ledger.jsonl').read_bytes()if(P/'runtime/ledger.jsonl').exists()else b'';events=[json.loads(x)for x in raw.splitlines()];require(raw.endswith(b'\n') and len(events)==38 and events[-1]['kind']=='result','exact terminal284 checkpoint');rps=[x['receipt']for x in events if x['kind']=='result'];current=[json.loads(Path(p['path']).read_bytes())for p in rps];require(len(current)==19 and all(r['status']=='passed' for r in current) and current[-1]['all_attempts']==2332,'exact34 passed predecessor jobs');require(all(r['cleanup']['clean']and r['cleanup']['leader_reaped']for r in current),'owned cleanup');receipts=history['receipts']+rps;rs=[json.loads(Path(p['path']).read_bytes())for p in receipts];require(len(rs)==2332 and sum(r['status']=='failed'for r in rs)==156,'all consumed history');require(not S.exists(),'fresh successor');S.mkdir();entries={};links={}
partials=[W/'mac-carried-proof-cache249-source01',W/'mac-arithmetic-selection252-source01',W/'mac-arithmetic-selection252-source02',W/'mac-arithmetic-selection254-source01',W/'mac-arithmetic-selection252-source04',W/'mac-merkle-arithmetic-construction253-source01',W/'mac-merkle-candidate255-source01',W/'mac-merkle-position-global190-source01',W/'mac-merkle-integer-root191-source01',W/'mac-merkle-field-fold196-source01',W/'mac-registry-semantic-sound205-source01',W/'mac-prefix-candidate258-source01',W/'mac-registry-semantic-sound205-source02']
for p in [p for root in[P,*partials]for p in root.rglob('*')]:
 if p.is_symlink():v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
for key,v in json.loads((storage/'archive-map01.json').read_bytes())['records'].items():
 if any(key.startswith(str(root)+'/')for root in[P,*partials]):entries[key]=v['original']
put('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(root)for root in[P,*partials]],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(rps,current):
 if r['status']!='passed':continue
 n=r['module'];cache=Path(r['command'][r['command'].index('-o')+1]).parent;c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
predecessor=(P/'maintained/guard.py').read_bytes();require(hashlib.sha256(predecessor).hexdigest()=='d38270306c68c5353fe12a9433a67cf02793c1fd1be75593e2a8a40e94004d9a','exact preserved executor');old=predecessor;require(pin(storage/'archive-map01.json')['sha256']=='c200981f686cb8677ed63e0b55138a17bbb57d9dd8234d8cef4e7571ccb533d5','exact retained storage map');fixture=W/'mac-directory-census-cache219b-source01/fixtures/ordinary/link';require(str(fixture)not in c['static_records'] and fixture.is_symlink(),'alias remains separately closed; no ordinary symlink pin')
ast.parse(old)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes(old);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());put('maintained-inventory01.json',{p.name:pin(p)for p in(S/'maintained').iterdir()})
for root in [*[W/('mac-history-metadata-preservation126-'+str(i))for i in[37]],W/'mac-directory-census-cache219b-source01',W/'mac-captured-canonical217-source02',W/'mac-canonical-comparisons216-source01',W/'mac-canonical-comparisons216-data01',*[W/('mac-canonical-comparisons216-source'+str(i).zfill(2))for i in[2,3,4,5,6]]]:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file() and not p.is_symlink():c['static_records'][str(p)]=pin(p)
# Restore only genuinely UNRUN original level interfaces after the experimental32 topology.
for output in json.loads((W/'mac-merkle-global-level185-source01/generation01.json').read_bytes())['outputs']:
 n=output['name'];
 if n in c['qualified_batch_imports']:continue
 require(pin(output['source']['path'])==output['source'],'exact original level source');c['modules'][n]=dict(source=output['source'],source_root=str(W/'mac-merkle-global-level185-source01/source-root'),audits=output['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(output['source']['path']).read_text(),re.M))
newnames=[]
for root in [W/'mac-merkle-middle239-source01',W/'mac-merkle-global240-source01',W/'mac-merkle-compose241-source03',W/'mac-merkle-conservative235-source01',W/'mac-canonical-inputs222-source01',W/'mac-registry-sparse244-source01',W/'mac-merkle-sparse243-source02',W/'mac-merkle-first-sparse245-source02',W/'mac-merkle-first-hash248-source01',W/'mac-word-compatibility250-source01',W/'mac-arithmetic-selection252-source05',W/'mac-merkle-arithmetic-construction253-source02',W/'mac-collection-candidate256-source01',W/'mac-merkle-candidate255-source02',W/'mac-merkle-position-global190-source02',W/'mac-merkle-integer-root191-source02',W/'mac-packed-candidate257-source01',W/'mac-merkle-field-fold196-source02',W/'mac-indexed-candidate260-source01',W/'mac-registry-semantic-sound205-source03',W/'mac-prefix-candidate258-source02',W/'mac-candidate-batches262-source01',W/'mac-candidate-collectors259-source03',W/'mac-candidate-path261-source01']:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file() and not p.is_symlink():c['static_records'][str(p)]=pin(p)
 generation=json.loads((root/'generation01.json').read_bytes())
 for output in generation['outputs']:
  require(pin(output['source']['path'])==output['source'],'exact maintained successor bytes');n=output['name'];c['modules'][n]=dict(source=output['source'],source_root=str(root/'source-root'),audits=output['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(output['source']['path']).read_text(),re.M));newnames.append(n)
original=prior['order'];order=[n for n in original if n not in c['qualified_batch_imports'] and n not in ['CanonicalRepresentation219','CapturedMerkleNoncomp223Pilot','CapturedMerkleGlobalArithmetic184L01B20','CapturedMerkleGlobalArithmetic184L01B22','CapturedMerkleGlobalArithmetic184L01B23','CapturedMerkleSmall227Pilot','CapturedMerkleLocal229Pilot']];order=[n for n in order if n not in ['CapturedMerkleLocal236Certificate','CapturedMerkleLocal236Global','CapturedMerkleGlobalArithmetic184L01B21','CapturedMerkleCompose241']];require(order[0]=='CandidateRows258P037' and len(order)==195,'exact remaining214 prefix pieces');sparse={}
for root in [W/'mac-registry-sparse244-source01',W/'mac-merkle-sparse243-source02',W/'mac-merkle-first-sparse245-source02']:
 for d in json.loads((root/'position-map01.json').read_bytes())['chunks']:sparse[d['global_module']]=d['local']
order=[n for n in order if n not in set(sparse.values())];order=[x for n in order for x in ([sparse[n],n] if n in sparse else [n])];order=order;require('CapturedMerkleFirstHash248'in c['qualified_batch_imports'],'accepted thin248 retained without replay');require(len(order)==len(set(order)),'exact interleaved one-name topology')
for root in [W/'mac-shared-word-flags220-source01',W/'mac-shared-word-flags220-source02',W/'mac-shared-word-flags220-source03',W/'mac-shared-word-witness221-source01',W/'mac-shared-word-witness221-source02',W/'mac-shared-word-witness221-source03',W/'mac-merkle-wide223-source01',W/'mac-merkle-wide223-source02',W/'mac-merkle-wide223-source03',W/'mac-merkle-wide224-source01',W/'mac-merkle-paired225-source01',W/'mac-merkle-paired226-source01']:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file() and not p.is_symlink():c['static_records'][str(p)]=pin(p);require(len(order)==len(set(order)),'remaining exact no-replay topology')

for root in [W/'mac-merkle-sparse243-source02',W/'mac-merkle-first-sparse245-source01',W/'mac-merkle-first-sparse245-source02',W/'mac-registry-global175-176-kernel-result01',W/'mac-merkle-first186-kernel-result01',W/'mac-merkle-level0-243-kernel-result01',W/'mac-merkle-level1-243-kernel-result01',W/'mac-merkle-level2-243-kernel-result01',W/'mac-merkle-level3-243-kernel-result01',W/'mac-merkle-level4-243-kernel-result01',W/'mac-merkle-first-hash248-kernel-result01']:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file()and not p.is_symlink():c['static_records'][str(p)]=pin(p)
order=['CandidateBatch262B'+str(i).zfill(2) for i in range(13)]+['CompilerCandidateAssembly259','CandidateCall04Rows259','CandidatePriorRows259','CandidateThreeCallRows259','CandidateRegistryRows259','CandidateFirstMerkleRows259','CandidateMerkleSelection261','CandidateMerklePrior261','CandidateMerkleRest261','CandidateMerkleMeaning261'];require(all(n in c['modules'] and n not in c['qualified_batch_imports'] for n in order),'exact23 new physical modules; no accepted replay');
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=order);c['charged_roots'].extend([str(S),*map(str,partials)]);c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
serial=(P/'dispatcher/serial.py').read_text();needle=" c=g['read_config'](str(config),pin(config)['sha256']);require(c['static_records'][str(Path(__file__))]==pin(Path(__file__)),'exact executing dispatcher')\n";require(serial.count(needle)==1,'exact singleton startup resolver');require(serial.count('1<=args.max_jobs<=512')==1,'exact prior finite administrative chunk');ast.parse(serial);(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_text(serial)
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

baseline={'__name__':'SOURCE_DATA_ONLY','__file__':str(P/'maintained/guard.py')};exec(compile((P/'maintained/guard.py').read_bytes(),str(P/'maintained/guard.py'),'exec'),baseline)
root=str(P);before=set(baseline['phase_files'](root));after=set(ns['phase_files'](root));require(before==after,'exact entire immutable predecessor file/link keyset')
aliases=json.loads((P/'overlay-manifest01.json').read_bytes())['aliases'];v0=baseline['bytes_in'](root,aliases);v1=ns['bytes_in'](root,aliases);require(v0==v1,'exact predecessor physical and metadata byte census');ns['directory_phase_close']()
put('directory-census-DATA01.json',dict(scope='Pure helper old/new complete immutable predecessor keyset/link/physical/metadata census comparison; no verifier/helper entrypoint launch.',equal=True,files_links=len(before),physical=v1[0],metadata=v1[1],directory_cache_bytes=ns['_DIRECTORY_CACHE_BYTES'],old_guard=pin(P/'maintained/guard.py'),new_guard=pin(S/'maintained/guard.py')))
put('transition-observation01.json',dict(old_phase=str(P),ledger=pin(P/'runtime/ledger.jsonl'),observed=rps,scope='28519 jobs2314..2332/P018..P036 all passed; owned SIGTERM cancellation sent at balanced38 events/no-heavy checkpoint, dispatcher stopped in outer cancelled() before a further claim. All2332 attempts156 failures and37 accepted258 namespaces retained. New262 groups195 untouched original namespace/theorem/proof bodies into13 physical modules, deduplicating only identical finite preambles/headers. New25903 changes ONLY import headers to actual262 physical names, all259 theorem bodies unchanged; old25902 UNRUN preserved. New261 four symbolic selection/prior/rest/output candidate joins eight UNRUN audits. Guard bytes d382/storage37 identical; per-run physical protections unchanged. No olean alias under a false module identity, no accepted replay, no reset.'))
put('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],remaining_named=len(order),new_names=newnames,guard=pin(S/'maintained/guard.py'),no_accepted_replay=True,scope='Autonomous actual canonical recovery + remaining Boolean/word/hash global obligations. Same per-run physical safeguards; finite serial dispatcher ceiling512 replaces administrative128 only, reducing repeated history/config copies; no cumulative project quota.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),failures=156,first=order[:4],remaining=len(order),config=pin(S/'config01.json'),guard=pin(S/'maintained/guard.py'),producer=pin(S/'producer-manifest01.json'),physical=sum(p.stat().st_size for p in S.rglob('*')if p.is_file()))))
