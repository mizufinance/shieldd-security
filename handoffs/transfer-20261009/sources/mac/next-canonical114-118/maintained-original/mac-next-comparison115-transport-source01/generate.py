from pathlib import Path
import sys,re,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'sealed refresh refusal')
binding=json.loads((S/'source-binding01.json').read_bytes())
for key in ['old','target','numeric_template']:require(pin(Path(binding[key]['path']))==binding[key],'exact source inputs before emission')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);outputs=[]
def emit(name,t,audits):
 require(len(t.encode())<=262144,'finite source')
 t+='\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in audits)
 p=r/(name+'.lean');p.write_text(t);outputs.append(dict(name=name,source=pin(p),audits=audits))
emit('NextComparison115Rename',(S/'rename-template.lean').read_text(),['ShielddSecurity.NextComparison115.rename','ShielddSecurity.NextComparison115.copy_fixed'])
for j in range(8):
 old='CapturedValueComparison102Pilot'if j==0 else f'CapturedValueComparison104C{j:02d}'
 name=f'NextComparison115Rows{j:02d}';length=60 if j==7 else 64;start=10524+64*j
 t=f"""import ShielddSecurity.NextComparison115Rename
import ShielddSecurity.{old}
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
noncomputable def actualRows : List Row := CompilerColumnRenaming05.rows NextComparison115.rename {old}.actualRows
theorem rows_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} {length} actualRows=true := by decide +kernel
theorem selected_satisfies {{F : Type}} [Field F] (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Satisfies rho actualRows :=
  CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} {length} actualRows rows_checked (by decide) rho arithmetic
end ShielddSecurity.{name}
"""
 emit(name,t,['ShielddSecurity.'+name+'.'+n for n in ['actualRows','rows_checked','selected_satisfies']])
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),scope='Nine nextValue exact row transport modules; selected_numeric is inherited from qualified110. Final canonical/assertion/shared constructor separate.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=len(outputs),audits=sum(len(o['audits'])for o in outputs))))
