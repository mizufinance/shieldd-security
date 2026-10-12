from pathlib import Path
import json,hashlib,importlib.util
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-candidate-ordered250-256-kernel-result01'
spec=importlib.util.spec_from_file_location('preserved',J.parent/'read_preserved_mac_config13.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
checked={}
def read(pin):
 p=Path(pin['path']);b=p.read_bytes()if p.exists()else preserved.read_config(p,pin)
 assert len(b)==pin['bytes']and hashlib.sha256(b).hexdigest()==pin['sha256'];checked[str(p)]=pin;return b
deps=json.loads((P/'dependencies01.json').read_text());h=json.loads(read(deps['history']));ledger=json.loads((P/'ledger-prefix01.json').read_text());read(deps['current_config']);read(deps['storage_map'])
carried=len(h['receipts']);assert carried==h['consumed_attempts']==ledger['carried_attempts']
records=[]
for p,status in zip(h['receipts'],h['expected_statuses']):
 r=json.loads(read(p));assert r['status']==status and status in ['passed','failed'];assert r['cleanup']['clean'];records.append((p,r))
assert len(h['expected_statuses'])==carried
assert abs(sum(r['lean_seconds']for _,r in records)-h['consumed_lean_seconds'])<1e-7
events=ledger['events'];assert len(events)>0 and len(events)%2==0
for intent,result in zip(events[::2],events[1::2]):
 assert intent['kind']=='intent'and result['kind']=='result';r=json.loads(read(result['receipt']));assert r['status']=='passed'and r['module']==intent['module']and r['source']==intent['source']and r['command']==intent['command'];records.append((result['receipt'],r))
assert len(records)==ledger['endpoint_attempt']
assert len({p['path']for p,_ in records})==len(records)
failed=[]
for p,r in records:
 if r['status']=='passed':continue
 assert r['error']is not None
 for k in ['source','stdout','stderr']:
  if r.get(k)is not None:read(r[k])
 failed.append(dict(receipt=p,module=r['module'],source=r.get('source'),stdout=r.get('stdout'),stderr=r.get('stderr'),exit=r.get('exit'),error=r['error'],scope='Rejected original attempt; no semantic control claim'))
assert len(failed)==sum(r['status']=='failed'for _,r in records)
assert all(e['receipt']in [p for p,_ in records]for e in json.loads((P/'source-object-receipt01.json').read_text()))
for z in deps['inputs'].values():read(z)
report=dict(status='PASSED',kind='Complete original receipt/history/endpoint provenance and exact source dependency pins, no Lean replay',attempts=len(records),passed=sum(r['status']=='passed'for _,r in records),failed=len(failed),rejected=failed,pins_rehashed=len(checked),qualified_modules=6,complete_reports=19,scope='Original complete history through selected six-module endpoint and all prior failed source/log preserved; no source/Lean/object alteration',full_transfer='OPEN')
(J/'source-history-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='rejected'}))
