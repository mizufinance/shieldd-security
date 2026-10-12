"""Whole checked walk and absence-initialized block driver; original proof repairs, no verifier."""
from pathlib import Path
import argparse,json,hashlib,re
J=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('label',choices=['checked-word-walk','checked-word-block-driver']);a=p.parse_args();walk=a.label=='checked-word-walk'
D=J/('windows-'+a.label+'-review01');P=D/'packet01';M='TransferCheckedWordWalk01' if walk else 'TransferCheckedWordBlockDriver01';S=P/'source/ShielddSecurity'/(M+'.lean');s=S.read_text();count=4 if walk else 5
def read(p):return json.loads(p.read_text())
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=read(P/'qualified/plan.json');assert all(pin(S)[k]==plan['targets'][0]['source'][k] for k in ['bytes','sha256'])
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',s,re.M)==re.findall(r'^#check @([^\n]+)',s,re.M)and s.count('#check @')==count
events=[json.loads(x)for x in(P/'qualified/events.jsonl').read_text().splitlines()];assert len(events)==2 and events[-1]['result']['status']=='passed'
records=[]
if walk:
 assert not list(P.glob('rejected-*'))
 for token in ['| writes, [] => .ok (.ok writes)','(nullifyAtKey backend child parent writes key batch.1 batch.2).bind','| .ok next => walk backend child parent key next rest','(invariant : Invariant blockCapacity (previousPending ((overlay parent writes) key)))','returned_public_batch_derives_empty_identity_or_nonempty_source_and_stage','returned_stage_at_key_derives_exact_returned_object_and_one_cache_write','invariant.1 invariant.2.1 staged','batches.flatMap (fun batch => batch.1.map','backend.lookup child nullifier = some false','nextInvariant restReturned']:assert token in s
 scope='Returned whole checked public batch walk derives actual final selected-slot Invariant, exact original ordered key append, every modeled durable lookup=false and all other-key write/view frames. Empty batch identity and nonempty source/stage access are derived from the returned public nullify result, with actual selected cache write and inductive invariant propagation. Prior Invariant is an explicit helper premise; initialization owns its discharge. No caller intermediate successful stages, selected typed Open, desired next object, getter-success, admission or codec inverse. Canonical fields/functional cache/backend/source observation are declared model interfaces; actual native source selector/Any/Clone/imbl/Scalar/reader/compiler/async/ownership/full control trace remain owned OPEN. First attempt passed, original inherited failures retained. No replay/native execution; full Transfer/combined replay OPEN.'
else:
 for token in ['batches.flatMap Prod.fst','(walk backend child parent key writes batches).bind','| .ok staged => (sealAtKey parent staged key).map','(initiallyAbsent : (overlay parent writes) key = none)','(returned : run backend child parent writes key batches = .ok (.ok final))','empty_pending_invariant blockCapacity','initialInvariant walked','fields = allFields batches','canonical_source_scalar_list_recovers_exact_ordered_original_fields','(allFields batches).length ≤ blockCapacity','sourceOrdered ((overlay parent final) key) = .ok (allFields batches)','sourceIsSealed ((overlay parent final) key) = .ok true','sourceEnsureSealed ((overlay parent final) key) = .ok (.ok ())']:assert token in s
 change='      change (sealAtKey parent staged key).map (fun result => result.mapError (fun _ => BatchError.sealed)) = .ok (.ok final) at returned\n'
 for i in [1,2]:
  q=P/f'rejected-checked-block-attempt{i:02d}';old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
  fixed=old.replace('exact ⟨staged, rfl, rfl⟩','exact ⟨staged, rfl, sealing⟩')
  if i==1:fixed=fixed.replace('    | ok staged =>\n      cases sealing :','    | ok staged =>\n'+change+'      cases sealing :')
  assert fixed==s
  es=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(es)==2 and es[-1]['result']['status']=='failed' and es[-1]['result']['seconds']<240
  assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
  assert read(q/'plan.json')['pressure_limits']==plan['pressure_limits'] and read(q/'plan.json')['limits']==plan['limits']
  logs=list(q.glob('runs/*/stdout.txt'));assert len(logs)==1
  assert ('Tactic `rewrite` failed' if i==1 else 'Application type mismatch') in logs[0].read_text()
  records.append(dict(result=es[-1]['result'],source=pin(q/'handwritten'/(M+'.lean')),events=pin(q/'events.jsonl'),stdout=pin(logs[0]),repair='Proof-only explicit normalization of Except bind/map and reuse of actual sealing equation. Definitions and theorem contracts unchanged. Entire failed attempts retained.'))
 scope='Returned whole source-shaped checked block run derives actual successful walk then checked seal. Observed initial selected absence discharges the helper Invariant; exact canonical list recovery derives the final Sealed original global field list, all three actual modeled SCT getters, capacity, unique keys, every durable false lookup and all other-key frames. Only observed initial absence and returned whole run success are supplied: no caller intermediate walk/seal, invariant, desired field/getter, inverse or supported type-domain premise. Initialization from actual native snapshot remains owned and addressed separately. Functional views and CanonicalScalar are explicit model interfaces; native source selectors/Any/Clone/imbl/Scalar/reader/compiler/async/ownership/full control/error/recovery trace remain OPEN. Two original proof failures retained; fixes only normalize the result expression and supply its actual sealing equation, with unchanged definitions/contracts/guards. No replay/native execution; full Transfer/combined replay OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY'if records else'PASSED_SOURCE_SCOPE',source=pin(S),fresh_reports=count,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN',kind='Independent complete source/premise and original proof-repair review; no verifier')
(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],module=M,reports=count,rejected=len(records))))

