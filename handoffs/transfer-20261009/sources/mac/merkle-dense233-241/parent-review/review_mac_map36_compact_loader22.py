from pathlib import Path
import ast,json,hashlib,lzma,re
J=Path(__file__).parent;W=J.parent
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(data):
 def unique(items):
  d={}
  for k,v in items:assert k not in d;d[k]=v
  return d
 return json.loads(data,object_pairs_hook=unique)
old=W/'mac-history-metadata-preservation126-31/archive-map01.json';new=W/'mac-history-metadata-preservation126-36/archive-map01.json';prior=strict(old.read_bytes())['records'];data=strict(new.read_bytes());assert data['schema']=='exact-inactive-phase-metadata-storage02';records=data['records'];assert all(records[k]==v for k,v in prior.items());assert len(prior)==440 and len(records)==661
total=0;packed=0
for k,v in records.items():
 assert re.fullmatch(str(W)+r'/mac-full-arithmetic45-execution[0-9]+/(config01|protected-history01|overlay-manifest01)\.json',k)and v['original']['path']==k
 o=v['original'];a=v['archive'];p=Path(a['path']);assert p.is_file()and not p.is_symlink()and 0<o['bytes']<=16*1024*1024
 b=p.read_bytes();assert len(b)==a['bytes']and hashlib.sha256(b).hexdigest()==a['sha256'];dec=lzma.LZMADecompressor(memlimit=128*1024*1024);out=dec.decompress(b,max_length=o['bytes']+1);assert dec.eof and not dec.unused_data and len(out)==o['bytes']and hashlib.sha256(out).hexdigest()==o['sha256'];assert isinstance(strict(out),dict);assert v['mode']==420 and isinstance(v['mtime_ns'],int);assert not Path(k).exists();total+=len(out);packed+=len(b)
mapreview=dict(status='PASSED',kind='Independent exact append-only inactive metadata archive review',baseline=pin(old),successor=pin(new),records=661,prior_records_exact=440,original_bytes=total,archive_bytes=packed,scope='Only inactive configs/history/overlay manifests; exact original size/SHA and retained mode/mtime, bounded EOF/trailing decode; no source/object/receipt fallback',full_transfer='OPEN');(J/'mac-inactive-phase-map36-review22.json').write_text(json.dumps(mapreview,indent=2)+'\n')
baseline=W/'mac-full-arithmetic45-execution228/maintained/guard.py';successor=W/'mac-full-arithmetic45-execution234/maintained/guard.py';a=ast.parse(baseline.read_text());b=ast.parse(successor.read_text())
def normalized(t):
 result=[]
 for n in t.body:
  if isinstance(n,ast.Assign)and any(isinstance(v,ast.Name)and v.id=='_STORAGE_PIN'for v in n.targets):continue
  if isinstance(n,ast.FunctionDef)and n.name=='read_config':continue
  if isinstance(n,ast.FunctionDef)and n.name=='preserved_configs':
   for c in ast.walk(n):
    if isinstance(c,ast.Constant)and isinstance(c.value,str):c.value=c.value.replace('|overlay-manifest01','')
  if isinstance(n,ast.FunctionDef)and n.name=='execute':
   for c in ast.walk(n):
    if isinstance(c,ast.Assign)and any(isinstance(v,ast.Name)and v.id=='config'for v in c.targets)and isinstance(c.value,ast.Call)and isinstance(c.value.func,ast.Name)and c.value.func.id=='read_config':c.value.func.id='read_bound'
  result.append(ast.dump(n,include_attributes=False))
 return result
assert normalized(a)==normalized(b)
source=ast.parse(successor.read_text());fn=next(n for n in source.body if isinstance(n,ast.FunctionDef)and n.name=='read_config')
def require(ok,msg):
 if not ok:raise ValueError(msg)
def read_identity(identity):
 p=Path(identity['path'])
 if p.exists():raw=p.read_bytes()
 else:
  r=records[str(p)];assert r['original']==identity;raw=lzma.decompress(Path(r['archive']['path']).read_bytes(),memlimit=128*1024*1024)
 assert len(raw)==identity['bytes']and hashlib.sha256(raw).hexdigest()==identity['sha256'];return raw
controls=[];saved={}
ns=dict(require=require,strict_json=strict,read_pin=read_identity,json=json,sha=lambda v:hashlib.sha256(v).hexdigest(),read_bound=lambda path,digest:saved['wrapper']);exec(compile(ast.Module(body=[fn],type_ignores=[]),'<isolated-pure-config-loader>','exec'),ns)
original=records[str(W/'mac-full-arithmetic45-execution234/config01.json')]['original'];wrapper=strict(read_identity(original));saved['wrapper']=wrapper;result=ns['read_config']('unused','unused');base=strict(read_identity(wrapper['base']));expected={**base,**wrapper['replace']}
for k,v in wrapper['merge'].items():expected[k]={**base[k],**v}
assert result==expected;encoded=(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n').encode();assert len(encoded)==wrapper['effective_bytes']and hashlib.sha256(encoded).hexdigest()==wrapper['effective_sha256']
for label,mutate in [('wrong-effective',lambda w:w.update(effective_sha256='0'*64)),('unknown-key',lambda w:w['replace'].update(unknown=True)),('overlap',lambda w:w['merge'].update(order={})),('wrong-base',lambda w:w['base'].update(sha256='0'*64)),('nested-base',lambda w:w.update(base={'path':'nested','bytes':1,'sha256':'0'*64})),('trailing-key',lambda w:w.update(extra=True))]:
 saved['wrapper']=strict(json.dumps(wrapper));mutate(saved['wrapper'])
 try:ns['read_config']('unused','unused')
 except (AssertionError,ValueError,KeyError):controls.append(label)
 else:raise AssertionError(label)
report=dict(status='PASSED',baseline=pin(baseline),successor=pin(successor),storage_map=pin(W/'mac-history-metadata-preservation126-35/archive-map01.json'),independent_map_review=pin(J/'mac-inactive-phase-map36-review22.json'),config_wrapper=original,effective_bytes=len(encoded),effective_sha256=hashlib.sha256(encoded).hexdigest(),pure_negative_controls=controls,scope='Sole AST deltas are exact storage pin/archive overlay metadata extension and bounded deterministic config reconstruction; all physical/prelaunch/postflight/one-process checks identical. Original archived base and explicit replace/closed map merge authenticate entire effective configuration. No guard execution, Lean or worker state mutation',full_transfer='OPEN');(J/'mac-compact-config-guard-review22.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',records=661,controls=len(controls),effective_bytes=len(encoded))))
