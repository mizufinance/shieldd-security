"""Closed, isolated, in-memory source replay only. No Lean/cache/source copies."""
from pathlib import Path
import argparse,hashlib,json,io,sys,contextlib

def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 require(p.is_file()and not p.is_symlink(),'ordinary input');b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(b):
 def pairs(xs):
  d={}
  for k,v in xs:require(k not in d,'duplicate key');d[k]=v
  return d
 return json.loads(b,object_pairs_hook=pairs)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated unoptimized interpreter')
p=argparse.ArgumentParser()
for k in ['inventory','inventory-sha256','expected','expected-sha256','qualification','extra','coefficients','data-directory','coefficient-source','report']:p.add_argument('--'+k,required=True)
a=p.parse_args();s=Path(__file__).resolve().parent
inventory=Path(a.inventory);require(pin(inventory)['sha256']==a.inventory_sha256,'inventory hash');mi=strict(inventory.read_bytes())
def closed():
 require({x.name for x in s.iterdir()}==set(mi),'exact closed maintained listing')
 for n,v in mi.items():
  x=s/n;require(all(pin(x)[k]==v[k]for k in ['sha256','bytes']),'maintained hash')
closed();expected=Path(a.expected);require(pin(expected)['sha256']==a.expected_sha256,'expected source hashes');wanted=strict(expected.read_bytes());require(len(wanted)==90,'exact ninety-source output domain')
virtual=Path(a.report).parent/'VIRTUAL-SOURCE-REPLAY-NEVER-CREATED';require(not virtual.exists(),'no physical virtual root')
oldopen,oldread,oldmkdir=Path.open,Path.read_bytes,Path.mkdir;captured={}
class Sink(io.BytesIO):
 def __init__(self,p):super().__init__();self.p=p
 def close(self):
  captured[str(self.p)]=self.getvalue();super().close()
def op(path,*args,**kw):
 if args and args[0]=='xb'and path.is_relative_to(virtual):return Sink(path)
 return oldopen(path,*args,**kw)
def read(path):
 if str(path)in captured:return captured[str(path)]
 return oldread(path)
def mkdir(path,*args,**kw):
 if path.is_relative_to(virtual):return None
 return oldmkdir(path,*args,**kw)
code=(s/'generate.py').read_bytes();savedargv=sys.argv[:]
try:
 Path.open=op;Path.read_bytes=read;Path.mkdir=mkdir
 sys.argv=['generate.py','--output',str(virtual),'--qualification',a.qualification,'--extra',a.extra,'--coefficients',a.coefficients,'--data-directory',a.data_directory,'--coefficient-source',a.coefficient_source]
 with contextlib.redirect_stdout(io.StringIO()):exec(compile(code,str(s/'generate.py'),'exec'),{'__file__':str(s/'generate.py'),'__name__':'bounded_source_replay'})
finally:Path.open=oldopen;Path.read_bytes=oldread;Path.mkdir=oldmkdir;sys.argv=savedargv
require(set(Path(x).stem for x in captured if x.endswith('.lean'))==set(wanted),'exact output source keyset')
for path,b in captured.items():
 if path.endswith('.lean'):
  v=wanted[Path(path).stem];require(len(b)==v['bytes']and hashlib.sha256(b).hexdigest()==v['sha256'],'byte-exact source '+Path(path).stem)
closed();require(not virtual.exists(),'no physical source replay outputs')
result=dict(scope='DATA/source-byte replay only; zero Lean/kernel credit',sources=90,lean_source_bytes=sum(len(b)for x,b in captured.items()if x.endswith('.lean')),closed_maintained=True,recipe=pin(Path(__file__)),generator=pin(s/'generate.py'),inventory=pin(inventory),expected=pin(expected),qualification=pin(Path(a.qualification)))
with Path(a.report).open('x')as f:f.write(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(result))
