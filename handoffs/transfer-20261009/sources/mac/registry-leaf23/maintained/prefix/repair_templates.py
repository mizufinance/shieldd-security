"""Maintained template repair: omit unused CharP only; original packets immutable."""
import ast,hashlib,json,sys,zlib
from pathlib import Path
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent

def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def unique(v):
 d={}
 for k,x in v:require(k not in d,'duplicate JSON');d[k]=x
 return d
def decode(p,identity,limit):
 require(pin(p)==identity,'compressed pin before decode');z=zlib.decompressobj();b=z.decompress(p.read_bytes(),limit+1);require(len(b)<=limit and z.eof and not z.unused_data and not z.unconsumed_tail,'bounded EOF/trailing');return b
def load(stage,name):
 md=json.loads((stage/'producer-manifest01.json').read_bytes(),object_pairs_hook=unique)
 mi=json.loads((stage/'maintained-inventory01.json').read_bytes(),object_pairs_hook=unique)
 p=stage/'maintained'/name;b=decode(p,mi[name],65536)
 d=json.loads(decode(stage/'selected-data01.json.zlib',md['data'],262144),object_pairs_hook=unique)
 for x in d['pins']:require(pin(Path(x['path']))==x,'input source')
 return b.decode(),d
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated nonoptimized source generation')
a=R/'work/mac-registry-leaf20-source01';s,d=load(a,'fallback-source01.py.zlib')
needle=r'\ntheorem legal (base : Nat → F)'
require(s.count(needle)==1,'unique R0 template legal')
s=s.replace(needle,r'\nomit [CharP F p] in\ntheorem legal (base : Nat → F)')
n={'__name__':'repair_source','__file__':str(S/'repair_templates.py')};exec(compile(s,'maintained-R0-template-repair','exec'),n)
values=n['render'](d,n['loader'](a/'maintained'));require(n['render'](d,n['loader'](a/'maintained'))==values,'determinism')
a=R/'work/mac-registry-tail21-source01';s,d=load(a,'renderer21.py.zlib')
needle="t=old.read_text().split('\\nset_option pp.all true in\\n#check')[0]"
require(s.count(needle)==1,'unique maintained R1 template read')
s=s.replace(needle,needle+"\n t=exact(t,'\\ntheorem legal (base : Nat → F)','\\nomit [CharP F p] in\\ntheorem legal (base : Nat → F)')")
old='theorem legal (base : Nat → F) : Legal base steps := by simp [steps,materializedSteps,TransferPoseidonCall04Shared01.copyStep,Legal,Step.Legal]'
new='theorem legal (base : Nat → F) : Legal base steps := by\n  have build (ss : List Step) (b : Nat → F) (all : ∀ s∈ss,∀ value : Nat → F,s.Legal value) : Legal b ss := by\n    induction ss generalizing b with\n    | nil => trivial\n    | cons s ss ih => exact ⟨all s (by simp) b,ih (s.run b) (by intro t h;exact all t (List.mem_cons_of_mem s h))⟩\n  apply build\n  intro s member value\n  change s∈materializedSteps++[TransferPoseidonCall04Shared01.copyStep] at member\n  rcases List.mem_append.mp member with member|member\n  · obtain ⟨i,_,member⟩ := List.mem_flatMap.mp member\n    simp only [List.mem_cons,List.not_mem_nil,or_false] at member\n    rcases member with rfl|rfl|rfl <;> trivial\n  · have equal : s=TransferPoseidonCall04Shared01.copyStep := List.mem_singleton.mp member\n    subst s\n    rfl'
s=s.replace(" return {ns:data,"," t=exact(t,"+repr(old)+","+repr(new)+")\n return {ns:data,")
n={'__name__':'repair_source','__file__':str(S/'repair_templates.py')};exec(compile(s,'maintained-R1-template-repair','exec'),n)
more=n['render'](R,d);require(n['render'](R,d)==more,'determinism');values.update(more)
for name,b in values.items():
 prior=R/'work/mac-registry-leaf-kernel-continuation03/source-root/ShielddSecurity'/(name+'.lean')
 if not prior.exists():prior=R/'work/mac-registry-leaf-kernel-continuation02/source-root/ShielddSecurity'/(name+'.lean')
 old=prior.read_bytes()
 expected=old if name!='CapturedRegistryTail21R1Proof01' else old.replace(b'theorem legal (base : Nat \xe2\x86\x92 F) : Legal base steps := by simp [steps,materializedSteps,TransferPoseidonCall04Shared01.copyStep,Legal,Step.Legal]',b'theorem legal (base : Nat \xe2\x86\x92 F) : Legal base steps := by\n  have build (ss : List Step) (b : Nat \xe2\x86\x92 F) (all : \xe2\x88\x80 s\xe2\x88\x88ss,\xe2\x88\x80 value : Nat \xe2\x86\x92 F,s.Legal value) : Legal b ss := by\n    induction ss generalizing b with\n    | nil => trivial\n    | cons s ss ih => exact \xe2\x9f\xa8all s (by simp) b,ih (s.run b) (by intro t h;exact all t (List.mem_cons_of_mem s h))\xe2\x9f\xa9\n  apply build\n  intro s member value\n  change s\xe2\x88\x88materializedSteps++[TransferPoseidonCall04Shared01.copyStep] at member\n  rcases List.mem_append.mp member with member|member\n  \xc2\xb7 obtain \xe2\x9f\xa8i,_,member\xe2\x9f\xa9 := List.mem_flatMap.mp member\n    simp only [List.mem_cons,List.not_mem_nil,or_false] at member\n    rcases member with rfl|rfl|rfl <;> trivial\n  \xc2\xb7 have equal : s=TransferPoseidonCall04Shared01.copyStep := List.mem_singleton.mp member\n    subst s\n    rfl')
 require(b==expected,'only maintained omission change; DATA unchanged')
 if name.endswith('Proof01') or name.endswith('R1Data01'):
  p=S/'source-root/ShielddSecurity'/(name+'.lean')
  if p.exists():require(p.read_bytes()==b,'immutable replay')
  else:
   with p.open('xb')as f:f.write(b)
print(json.dumps({k:dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest()) for k,b in values.items()}))
