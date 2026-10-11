from pathlib import Path
import json,hashlib,importlib.util
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-captured-canonical217-kernel-result01'
spec=importlib.util.spec_from_file_location('preserved',J.parent/'read_preserved_mac_config13.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
checked={}
def read(pin):
 p=Path(pin['path']);b=p.read_bytes()if p.exists()else preserved.read_config(p,pin)
 assert len(b)==pin['bytes']and hashlib.sha256(b).hexdigest()==pin['sha256'];checked[str(p)]=pin;return b
deps=json.loads((P/'dependencies01.json').read_text());h=json.loads(read(deps['history']));ledger=json.loads((P/'ledger-prefix01.json').read_text());read(deps['current_config']);read(deps['storage_map'])
assert len(h['receipts'])==h['consumed_attempts']==ledger['carried_attempts']==1233
records=[]
for p,status in zip(h['receipts'],h['expected_statuses']):
 r=json.loads(read(p));assert r['status']==status and status in ['passed','failed'];assert r['cleanup']['clean'];records.append((p,r))
assert len(h['expected_statuses'])==1233
assert abs(sum(r['lean_seconds']for _,r in records)-h['consumed_lean_seconds'])<1e-7
events=ledger['events'];assert len(events)==2
for intent,result in zip(events[::2],events[1::2]):
 assert intent['kind']=='intent'and result['kind']=='result';r=json.loads(read(result['receipt']));assert r['status']=='passed'and r['module']==intent['module']and r['source']==intent['source']and r['command']==intent['command'];records.append((result['receipt'],r))
assert len(records)==ledger['endpoint_attempts']==1234
assert len({p['path']for p,_ in records})==1234
failed=[]
for p,r in records:
 if r['status']=='passed':continue
 assert r['error']is not None
 for k in ['source','stdout','stderr']:
  if r.get(k)is not None:read(r[k])
 failed.append(dict(receipt=p,module=r['module'],source=r.get('source'),stdout=r.get('stdout'),stderr=r.get('stderr'),exit=r.get('exit'),error=r['error'],scope='Rejected original attempt; no semantic control claim'))
assert len(failed)==ledger['endpoint_failures']==128
assert all(e['receipt']in [p for p,_ in records]for e in json.loads((P/'source-object-receipt01.json').read_text()))
for z in deps['inputs'].values():read(z)
report=dict(status='PASSED',kind='Complete original receipt/history/endpoint provenance and exact source dependency pins, no Lean replay',attempts=1234,passed=1106,failed=128,rejected=failed,pins_rehashed=len(checked),qualified_modules=1,complete_reports=5,scope='Original complete history and failed canonical recovery source/log preserved; no source/Lean/object alteration',full_transfer='OPEN')
(J/'source-history-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='rejected'}))
