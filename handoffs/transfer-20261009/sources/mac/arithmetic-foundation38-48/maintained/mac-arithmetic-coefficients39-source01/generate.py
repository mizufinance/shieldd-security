from pathlib import Path
import json,hashlib,sys
S=Path(__file__).resolve().parent
if not(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('isolated flags')
D=S/'coefficients01.json';raw=D.read_bytes()
if hashlib.sha256(raw).hexdigest()!='2de49e8a330defea76d11c36645b29a85f254c639166e71e286b3745cfa81332':raise ValueError('coefficient DATA pin')
d=json.loads(raw);cs=d['coefficients']
if len(cs)!=7483 or cs!=sorted(set(cs)):raise ValueError('closed coefficient index')
def tree(lo,hi):
 if hi-lo==1:return str(cs[lo])
 mid=(lo+hi)//2
 return '(if index<'+str(mid)+' then '+tree(lo,mid)+' else '+tree(mid,hi)+')'
names=[];records={};out=S/'source-root/ShielddSecurity';out.mkdir(parents=True)
for c in range(8):
 n='ArithmeticCoefficients39C'+str(c).zfill(2);names.append(n);lo=c*1024;hi=min(lo+1024,len(cs))
 t='import ShielddSecurity.CompilerFreshArithmetic35\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnamespace ShielddSecurity.'+n+'\ndef value (index : Nat) : Int := if '+str(lo)+'≤index ∧ index<'+str(hi)+' then '+tree(lo,hi)+' else 0\ntheorem first : value '+str(lo)+'='+str(cs[lo])+' := by decide +kernel\ntheorem last : value '+str(hi-1)+'='+str(cs[hi-1])+' := by decide +kernel\nend ShielddSecurity.'+n+'\n'
 for a in ['value','first','last']:t+='set_option pp.all true in\n#check @ShielddSecurity.'+n+'.'+a+'\n#print axioms ShielddSecurity.'+n+'.'+a+'\n'
 if len(t.encode())>262144:raise ValueError('module source bound')
 q=out/(n+'.lean')
 with q.open('xb')as f:f.write(t.encode())
 records[n]={'bytes':len(t.encode()),'sha256':hashlib.sha256(t.encode()).hexdigest()}
def outer(lo,hi):
 if hi-lo==1:return names[lo]+'.value index'
 mid=(lo+hi)//2
 return '(if index<'+str(mid*1024)+' then '+outer(lo,mid)+' else '+outer(mid,hi)+')'
n='ArithmeticCoefficients39';t=''.join('import ShielddSecurity.'+x+'\n'for x in names)+'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnamespace ShielddSecurity.'+n+'\ndef value (index : Nat) : Int := '+outer(0,8)+'\nend ShielddSecurity.'+n+'\nset_option pp.all true in\n#check @ShielddSecurity.'+n+'.value\n#print axioms ShielddSecurity.'+n+'.value\n'
q=out/(n+'.lean')
with q.open('xb')as f:f.write(t.encode())
records[n]={'bytes':len(t.encode()),'sha256':hashlib.sha256(t.encode()).hexdigest()}
with(S/'generation01.json').open('x')as f:json.dump({'data_sha256':hashlib.sha256(raw).hexdigest(),'modules':records,'order':names+[n],'scope':'balanced coefficient value store, no whole row proof'},f,sort_keys=True)
