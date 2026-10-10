from pathlib import Path
import json,hashlib,re
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=Path(__file__).resolve().parent;P=R/'mac-merkle-family32-selection-leaves03'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,d):
 with (S/n).open('x')as f:f.write(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n')
mods={};audits=[]
for rp in sorted((P/'runtime/receipts').glob('*.json')):
 d=json.loads(rp.read_bytes());require(d['status']=='passed'and d['cleanup']['clean']and type(d['exit'])is int and d['exit']==0,'passed clean')
 for a in d['audits']:
  require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'typehash');require(set(a['axioms'])<=set(['propext','Classical.choice','Quot.sound']),'standard');audits.append(dict(a,receipt=pin(rp)))
 names=re.findall(r'^\s*(?:def|theorem) (\w+)',Path(d['source']['path']).read_text(),re.M);require(set('ShielddSecurity.'+d['module']+'.'+n for n in names)==set(a['name']for a in d['audits']),'exact declaration census')
 mods[d['module']]={k:d[k]for k in['source','objects','stdout','stderr','lean_seconds','peak_group_rss','cleanup']};mods[d['module']].update(receipt=pin(rp),audits=len(d['audits']))
require(len(mods)==15 and len(audits)==186,'all15/186')
failed=[]
for path in ['mac-merkle-family32-selection-bodies02','mac-merkle-family32-selection-leaves01','mac-merkle-family32-selection-leaves02']:
 for rp in (R/path/'runtime/receipts').glob('*.json'):
  d=json.loads(rp.read_bytes());require(d['status']=='failed','failed history');failed.append(dict(receipt=pin(rp),source=d['source'],stdout=d['stdout'],stderr=d['stderr'],zero_credit=True,reason=d['error']))
put('qualified-modules01.json',mods);put('full-audits01.json',audits)
put('execution-census01.json',dict(accepted=15,audits=186,seconds=sum(x['lean_seconds']for x in mods.values()),peak_group_rss=max(x['peak_group_rss']for x in mods.values()),failed_predecessors=failed,ledger=pin(P/'runtime/ledger.jsonl')))
put('maintained-source-references01.json',[pin(p)for p in[P/'generate.py',P/'generation01.json',P/'prepare_continuation.py',R/'mac-merkle-family32-data01/extract.py',R/'mac-merkle-family32-data01/selected-data01.json',Path(__file__)]])
put('scope01.json',dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',qualified='Fifteen remaining source-ordered asset path selections, each12actual original arithmetic RowSpool bodies plus actual sharedcopy. Both canonical coverage directions checked; arbitrary-base linked-copy construction transfers to actual bodies; numeric segment write/support checked. Capturedindices metadata+independent DATA body association, not full-parent rowAt.',controls='Four same production-checker false facts on first target: coefficient+1(notmultipleofp), existing distinct rowindex0to1, omitted copyrow with full13mapping, altered copyrow. Refusals of finite identity checker, not semantic inequality.',open=['full16levelsameassignmentpath/anchor','formalglobalrowAt/fullrelation','Booleaninterpretationforremaininglevels/native/remainingassertions'],logs='Raw logs and objects retained locally only.'))
put('producer-manifest01.json',{p.name:pin(p)for p in S.iterdir()if p.is_file()})
put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),stage=pin(P/'producer-manifest01.json'),failed_history=pin(P/'protected-history01.json')))
require(all(pin(Path(d['path']))==d for d in json.loads((S/'producer-manifest01.json').read_bytes()).values()),'postseal');put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),all_entries_rehashed=True));print(json.dumps(dict(producer=pin(S/'producer-manifest01.json'),census=json.loads((S/'execution-census01.json').read_bytes()))))
