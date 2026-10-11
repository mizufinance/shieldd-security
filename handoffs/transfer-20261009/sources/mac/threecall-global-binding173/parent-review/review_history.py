from pathlib import Path
import json,hashlib,importlib.util
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-threecall-global-binding173-kernel-result01'
spec=importlib.util.spec_from_file_location('preserved',J.parent/'read_preserved_mac_config10.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
checked={}
def read(pin):
 p=Path(pin['path']);b=p.read_bytes()if p.exists()else preserved.read_config(p,pin)
 assert len(b)==pin['bytes']and hashlib.sha256(b).hexdigest()==pin['sha256'];checked[str(p)]=pin;return b
deps=json.loads((P/'source-dependencies01.json').read_text());h=json.loads(read(deps['carried_history']));ledger=json.loads((P/'ledger-snapshot01.json').read_text());read(deps['current_configuration']);read(deps['storage_map'])
assert len(h['receipts'])==h['consumed_attempts']==ledger['carried_attempts']==1185
records=[]
for p,status in zip(h['receipts'],h['expected_statuses']):
 r=json.loads(read(p));assert r['status']==status and status in ['passed','failed'];assert r['cleanup']['clean'];records.append((p,r))
assert len(h['expected_statuses'])==1185
assert abs(sum(r['lean_seconds']for _,r in records)-h['consumed_lean_seconds'])<1e-7
events=ledger['events'];assert len(events)==4
for intent,result in zip(events[::2],events[1::2]):
 assert intent['kind']=='intent'and result['kind']=='result';r=json.loads(read(result['receipt']));assert r['status']=='passed'and r['module']==intent['module']and r['source']==intent['source']and r['command']==intent['command'];records.append((result['receipt'],r))
assert len(records)==ledger['endpoint_attempts']==1187
assert len({p['path']for p,_ in records})==1187
failed=[]
for p,r in records:
 if r['status']=='passed':continue
 assert r['error']is not None
 for k in ['source','stdout','stderr']:
  if r.get(k)is not None:read(r[k])
 failed.append(dict(receipt=p,module=r['module'],source=r.get('source'),stdout=r.get('stdout'),stderr=r.get('stderr'),exit=r.get('exit'),error=r['error'],scope='Rejected original attempt; no semantic control claim'))
assert len(failed)==ledger['endpoint_failed']==124
assert all(e['receipt']in [p for p,_ in records]for e in json.loads((P/'source-object-receipt01.json').read_text()))
for z in deps['identity_records'].values():read(z)
report=dict(status='PASSED',kind='Complete original receipt/history/endpoint provenance and exact source dependency pins, no Lean replay',attempts=1187,passed=1063,failed=124,rejected=failed,pins_rehashed=len(checked),qualified_modules=144,complete_reports=867,scope='Original failures preserved; 867-vs866 initial sealer census refusal preserved separately, no source/Lean/object alteration',full_transfer='OPEN')
(J/'source-history-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='rejected'}))
