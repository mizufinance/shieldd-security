from pathlib import Path
import json,hashlib,re,shutil,subprocess
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
J=Path(__file__).resolve().parent
P=R/'mac-merkle-path33-kernel-result01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
checked={}
def verify(x):
 p=Path(x['path']);require(pin(p)==x,str(p));checked[str(p)]=x
def walk(x):
 if isinstance(x,dict):
  if set(['path','bytes','sha256'])<=x.keys():verify({k:x[k]for k in ['path','bytes','sha256']})
  else:
   for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
for name in ['maintained-references01.json','envelope01.json','execution-census01.json']:
 walk(json.loads((P/name).read_bytes()))
modules=json.loads((P/'qualified-modules01.json').read_bytes())
stages=['mac-segment-chain33-source02','mac-merkle-family32-tables04','mac-merkle-family32-whole06','mac-merkle-path33-source03','mac-merkle-path33-frame01','mac-merkle-path33-meaning03']
outputs={}
for stage in stages:
 source=R/stage;dest=J/(stage+'-regeneration01')
 if dest.exists():shutil.rmtree(dest)
 dest.mkdir();(dest/'source-root/ShielddSecurity').mkdir(parents=True)
 for name in ['generate.py','template.lean','extract.py','selected-data01.json']:
  if (source/name).is_file():shutil.copyfile(source/name,dest/name)
 result=subprocess.run(['python3','-I','-B','-S',str(dest/'generate.py')],capture_output=True,text=True)
 require(result.returncode==0,result.stdout+result.stderr)
 for path in (dest/'source-root/ShielddSecurity').glob('*.lean'):
  original=source/'source-root/ShielddSecurity'/path.name
  require(path.read_bytes()==original.read_bytes(),'generator mismatch '+path.name)
  expected=modules[path.stem]['source'];verify(expected)
  require(original.read_bytes()==Path(expected['path']).read_bytes(),'sealed generated source')
  outputs[path.stem]=dict(generated=pin(path),qualified=expected)
# Binding replay was prepared separately, including its sole necessary input-root rebinding.
B=J.parent/'merkle-family32-binding-review01/regeneration01'
for module,entry in modules.items():
 if module.startswith('MerkleFamily32Binding'):
  path=B/'source-root/ShielddSecurity'/(module+'.lean')
  require(path.read_bytes()==Path(entry['source']['path']).read_bytes(),'binding replay '+module)
  outputs[module]=dict(generated=pin(path),qualified=entry['source'])
require(set(outputs)==set(modules),'all22 reproduced')
# Match explicit public source declarations, with actual namespace nesting, to complete audits.
count=0
for module,entry in modules.items():
 stack=[];names=[];text=Path(entry['source']['path']).read_text()
 for line in text.splitlines():
  match=re.match(r'^namespace ([\w.]+)$',line)
  if match:stack.append(match[1]);continue
  if re.match(r'^end (?:[\w.]+)$',line):stack.pop();continue
  match=re.match(r'^\s*(?:def|theorem|abbrev|structure) (\w+)',line)
  if match:names.append('.'.join(stack+[match[1]]))
 receipt=json.loads(Path(entry['receipt']['path']).read_bytes())
 audited=[a['name']for a in receipt['audits']]
 require(len(names)==len(audited) and set(names)==set(audited),'complete declaration inventory '+module)
 count+=len(names)
result=dict(kind='parent exact maintained generator replay and complete explicit declaration census; no Lean',sources=outputs,provenance_pins_checked=len(checked),declarations=count,full_transfer='OPEN',full_row_instance='OPEN',native_correspondence='OPEN')
with(J/'endpoint-regeneration01.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(sources=len(outputs),provenance_pins=len(checked),declarations=count)))
