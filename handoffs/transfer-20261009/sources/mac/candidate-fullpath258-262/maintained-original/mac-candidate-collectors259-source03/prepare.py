from pathlib import Path
import json,hashlib,sys,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-candidate-collectors259-source02';B=W/'mac-candidate-batches262-source01';S=W/'mac-candidate-collectors259-source03'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source preparation');require(not S.exists(),'immutable');spec=json.loads((O/'templates01.json').read_bytes());mapping=json.loads((B/'namespace-map01.json').read_bytes())['bindings'];changes=[]
for n,d in spec['modules'].items():
 old=d['body'];lines=old.splitlines(keepends=True);new=[];seen=set()
 for line in lines:
  m=re.fullmatch(r'import ShielddSecurity\.(CandidateRows258P\d+)\n',line)
  if m:line='import ShielddSecurity.'+mapping[m[1]]['physical_module']+'\n'
  if line.startswith('import '):
   if line in seen:continue
   seen.add(line)
  new.append(line)
 d['body']=''.join(new)
 require(old[old.index('set_option autoImplicit'):]==d['body'][d['body'].index('set_option autoImplicit'):],'every original declaration/proof/audit namespace byte unchanged')
 changes.append(dict(module=n,old_body_sha256=hashlib.sha256(old.encode()).hexdigest(),new_body_sha256=hashlib.sha256(d['body'].encode()).hexdigest(),only_import_headers_changed=True))
for f in ['templates01.json','generation01.json','producer-manifest01.json']:spec['inputs'][str(O/f)]=pin(O/f)
for f in ['namespace-map01.json','generation01.json','producer-manifest01.json']:spec['inputs'][str(B/f)]=pin(B/f)
for output in json.loads((B/'generation01.json').read_bytes())['outputs']:spec['inputs'][output['source']['path']]=output['source']
spec['scope'].update(future_dependencies=[x['name']for x in json.loads((B/'generation01.json').read_bytes())['outputs']],import_layout='Physical batch262 modules expose unchanged195 original namespaces; first37 accepted258 objects reused. All259 declaration bodies unchanged from source02; no olean alias with a false module identity.',status='SOURCE_ONLY_UNRUN')
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'small source floor');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((O/'generate.py').read_bytes());put('import-delta01.json',changes);put('templates01.json',spec);print(json.dumps(dict(stage=str(S),modules=len(spec['modules']),only_import_headers_changed=True)))
