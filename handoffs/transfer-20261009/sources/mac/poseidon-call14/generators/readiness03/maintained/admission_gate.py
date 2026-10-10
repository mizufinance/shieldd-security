"""Owned per-module gate; durable local state requires the parent's external anchor."""
import fcntl,hashlib,json,os,time
from pathlib import Path
MODULES=['TransferPoseidonCall14B0R00Data01','TransferPoseidonCall14B0R00Column1Probe01']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def encoded(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def exclusive_write(path,payload):
 fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
 with os.fdopen(fd,'wb') as f:f.write(payload);f.flush();os.fsync(f.fileno())
class Gate:
 def __init__(self,ledger_directory,receipt_directory,genesis_sha256):
  self.directory=Path(ledger_directory);self.receipts=Path(receipt_directory);self.genesis_sha256=genesis_sha256
  self.lock=None;self._owns_lock=False;self.claim_entry=None;self.intent=None;self.authorized=None
 def assert_owned(self):
  assert self.lock is not None and self._owns_lock,'gate lock ownership required'
  os.fstat(self.lock)
 def acquire(self):
  assert self.lock is None and not self._owns_lock
  assert self.directory.is_dir() and not self.directory.is_symlink(),'missing/symlink ledger directory; no reinitialization'
  assert {p.name for p in self.directory.iterdir()}=={'genesis01.json','ledger.jsonl','run.lock','claims'},'ledger directory listing changed'
  for name in ['genesis01.json','ledger.jsonl','run.lock']:
   p=self.directory/name;assert p.is_file() and not p.is_symlink(),'ledger file missing/symlink'
  assert sha(self.directory/'genesis01.json')==self.genesis_sha256
  assert (self.directory/'claims').is_dir() and not (self.directory/'claims').is_symlink()
  descriptor=os.open(self.directory/'run.lock',os.O_RDWR|os.O_NOFOLLOW)
  try:fcntl.flock(descriptor,fcntl.LOCK_EX|fcntl.LOCK_NB)
  except BaseException:os.close(descriptor);raise
  # Publish ownership ONLY after flock succeeds. Losing descriptors are closed.
  self.lock=descriptor;self._owns_lock=True
 def release(self):
  if self.lock is not None:
   self.assert_owned()
   try:fcntl.flock(self.lock,fcntl.LOCK_UN)
   finally:os.close(self.lock);self.lock=None;self._owns_lock=False
 def state(self):
  self.assert_owned();raw=(self.directory/'ledger.jsonl').read_bytes();events=[];previous='0'*64;receipts={};claims={};intents={};consumed=0
  assert not raw or raw.endswith(b'\n'),'truncated ledger tail'
  for line in raw.splitlines(keepends=True):
   e=json.loads(line);assert encoded(e)==line,'noncanonical ledger framing'
   assert e['sequence']==len(events)+1 and e['previous_event_sha256']==previous,'ledger sequence/hash mismatch';previous=hashlib.sha256(line).hexdigest();events.append(e)
   kind=e['kind'];assert kind in ['claim_consumed','launch_intent','final']
   if kind=='claim_consumed':
    c=e['claim'];assert c['name'] not in claims;claims[c['name']]=c['sha256'];consumed+=1
   elif kind=='launch_intent':
    assert e['ordinal']==len(intents)+1 and e['module']==MODULES[e['ordinal']-1] and e['ordinal']<=2
    assert e['claim']['name'] in claims and claims[e['claim']['name']]==e['claim']['sha256'];assert e['receipt_name'] not in intents;intents[e['receipt_name']]=e
   else:
    assert e['receipt_name'] not in receipts and e['receipt_name'] in intents
    assert e['ordinal']==intents[e['receipt_name']]['ordinal'];receipts[e['receipt_name']]=e['receipt_sha256']
  assert {p.name for p in (self.directory/'claims').iterdir()}==set(claims),'missing/unaccounted admission claim; failclosed'
  for name,h in claims.items():p=self.directory/'claims'/name;assert p.is_file() and not p.is_symlink() and sha(p)==h,'claim changed'
  assert self.receipts.is_dir() and not self.receipts.is_symlink(),'receipt directory missing; no reset'
  actual={p.name:sha(p) for p in self.receipts.glob('build-*.json') if p.is_file() and not p.is_symlink()}
  assert actual==receipts,'ledger/complete launched receipt inventory mismatch';assert not any(p.is_symlink() for p in self.receipts.glob('build-*.json'))
  assert set(intents)<=set(receipts),'unfinalized launch intent; explicit reconciliation required'
  assert consumed==len(intents) and set(claims)=={e['claim']['name'] for e in intents.values()},'consumed claim without complete launch; explicit reconciliation required'
  return {'ledger_sha256':hashlib.sha256(raw).hexdigest(),'ledger_events':len(events),'launch_intents':len(intents),'consumed_claims':consumed,'receipts':receipts,'claims':claims,'genesis_sha256':self.genesis_sha256},events
 def append(self,event):
  self.assert_owned();p=self.directory/'ledger.jsonl';raw=p.read_bytes();lines=raw.splitlines(keepends=True);assert not raw or raw.endswith(b'\n')
  e=dict(event,sequence=len(lines)+1,previous_event_sha256=hashlib.sha256(lines[-1]).hexdigest() if lines else '0'*64)
  fd=os.open(p,os.O_WRONLY|os.O_APPEND|os.O_NOFOLLOW)
  with os.fdopen(fd,'ab') as f:f.write(encoded(e));f.flush();os.fsync(f.fileno())
  return e
 def authorize(self,admission,admission_sha256,module):
  assert admission.get('kernel_admission') is True,'explicit kernel admission required'
  self.acquire();state,events=self.state()
  assert admission['module']==module and module in MODULES,'single EXACT module admission required'
  ordinal=MODULES.index(module)+1
  # The external parent binds its latest durable state. Local storage alone
  # cannot defeat rollback/deletion of ALL state and ALL claim markers.
  assert state==admission['expected_prior_state'],'parent latest complete ledger/receipt/claim anchor mismatch'
  assert all(json.loads((self.receipts/n).read_text())['status']=='passed' for n in state['receipts']),'ANY prior nonpassed launched receipt => stop/refuse'
  assert not list(self.receipts.glob('build-'+module+'-*.json')),'same launched target receipt exists; replay/retry refused'
  assert admission['expected_ordinal']==ordinal==state['launch_intents']+1,'wrong expected ordinal'
  assert state['launch_intents']<2,'exact2probe launch-intent ceiling'
  if ordinal==2:
   prior=list(state['receipts']);assert prior==['build-'+MODULES[0]+'-01.json'],'Column1 requires exactly reviewed passed Data receipt'
   assert admission['reviewed_prior_data_receipt_sha256']==state['receipts'][prior[0]],'missing parent reviewed Data binding'
  assert not (self.directory/'claims'/(admission_sha256+'.json')).exists(),'admission reused'
  self.authorized={'admission_sha256':admission_sha256,'module':module,'ordinal':ordinal,'prior_state':state}
  return ordinal
 def begin(self,receipt,initial_result,command):
  self.assert_owned();assert self.authorized is not None and self.intent is None and self.claim_entry is None
  a=self.authorized;state,_=self.state();assert state==a['prior_state'],'state changed before claim consumption'
  assert receipt.parent.resolve()==self.receipts.resolve() and receipt.name=='build-'+a['module']+'-01.json'
  # Called only AFTER source/import preflight and the final volatile bounds
  # recheck under this owned lock. Refusals before begin do not consume claims.
  payload=encoded(a);name=a['admission_sha256']+'.json';exclusive_write(self.directory/'claims'/name,payload)
  self.claim_entry={'name':name,'sha256':hashlib.sha256(payload).hexdigest()}
  self.append({'kind':'claim_consumed','module':a['module'],'ordinal':a['ordinal'],'claim':self.claim_entry,'time_ns':time.time_ns()})
  exclusive_write(receipt,(json.dumps(initial_result,indent=2)+'\n').encode())
  self.intent=self.append({'kind':'launch_intent','module':a['module'],'ordinal':a['ordinal'],'receipt_name':receipt.name,'initial_receipt_sha256':sha(receipt),'claim':self.claim_entry,'command':command,'process_started':False,'time_ns':time.time_ns()})
  return self.intent
 def write_receipt(self,receipt,result):
  self.assert_owned();assert self.intent is not None,'no launched receipt update before durable intent'
  assert receipt.name==self.intent['receipt_name'] and receipt.parent.resolve()==self.receipts.resolve()
  assert receipt.is_file() and not receipt.is_symlink()
  receipt.write_text(json.dumps(result,indent=2)+'\n')
 def finalize(self,receipt):
  self.assert_owned();assert self.intent is not None,'only a durable launch intent can finalize a gated receipt'
  assert receipt.is_file() and not receipt.is_symlink() and receipt.name==self.intent['receipt_name'] and receipt.parent.resolve()==self.receipts.resolve()
  self.append({'kind':'final','module':self.intent['module'],'ordinal':self.intent['ordinal'],'receipt_name':receipt.name,'receipt_sha256':sha(receipt),'status':json.loads(receipt.read_text())['status'],'claim':self.claim_entry,'time_ns':time.time_ns()})
