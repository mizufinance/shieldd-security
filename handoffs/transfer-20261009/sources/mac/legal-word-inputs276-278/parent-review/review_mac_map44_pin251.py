from pathlib import Path
import json,ast,hashlib
J=Path(__file__).parent;W=J.parent
pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
a=W/'mac-full-arithmetic45-execution299/maintained/guard.py';b=W/'mac-full-arithmetic45-execution300/maintained/guard.py';assert pin(a)['sha256']=='7a402b18aec5ab5ba9231605876df05ef8d4b325bac54c50ccfb0920b1c21322';assert pin(b)['sha256']=='77e05e4eb1caeb76f58bf3dbfd45ebd7107391ac26b8ef2b464842c6d4e96b21';review=json.loads((J/'mac-storage-map44-review237.json').read_text());assert review['status']=='PASSED'
def split(p):
 pins=[];rest=[]
 for n in ast.parse(p.read_text()).body:
  if isinstance(n,ast.Assign)and any(isinstance(v,ast.Name)and v.id=='_STORAGE_PIN'for v in n.targets):pins.append(ast.literal_eval(n.value))
  else:rest.append(ast.dump(n,include_attributes=False))
 assert len(pins)==1;return pins[0],rest
ap,at=split(a);bp,bt=split(b);assert at==bt and ap==review['baseline_map']and bp==review['successor_map'];out=J/'mac-storage-map44-pin-guard-review251.json';assert not out.exists();out.write_text(json.dumps(dict(status='PASSED',baseline_guard=pin(a),successor_guard=pin(b),storage_review=pin(J/'mac-storage-map44-review237.json'),reader=pin(J/'read_preserved_mac_config20.py'),scope='Sole storage-map43→44 exact pin update. Every other top-level AST identical, including all verifier/admission/physical RAM/RSS/disk/heap/time/thread/cleanup/census/memoization rules. No Root guard or verifier execution.',full_transfer='OPEN'),indent=2)+'\n');print('PASSED sole exact storage pin; all other guard AST identical')
