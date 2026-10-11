from pathlib import Path
import json,hashlib,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-asset-comparison110-transport-source01'
if S.exists():raise ValueError('immutable source stage')
S.mkdir()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
old=W/'mac-registry-value-comparison102-source01/selected-data01.json';new=W/'mac-asset-comparison110-data01/selected-data01.json'
a=json.loads(old.read_bytes());b=json.loads(new.read_bytes())
def rename(x):return x+255 if 216<=x<471 else x+508 if 32246<=x<32754 else x
def terms(v):return sorted([[rename(x),c]for x,c in v])
for i,(o,n) in enumerate(zip(a['entries'],b['entries'])):
 if len(a['entries'])!=len(b['entries']) or n['bitColumn']!=rename(o['bitColumn']) or n['maximumBit']!=o['maximumBit'] or n['before']!=terms(o['before']) or n['after']!=terms(o['after']) or n['pivot']!=rename(o['pivot']) or n['auxiliary']!=rename(o['auxiliary']):raise ValueError('every entry exact source transport')
 for ro,rn in zip(o['rows'],n['rows']):
  if rn['a']!=terms(ro['a']) or rn['b']!=terms(ro['b']) or rn['index']!=ro['index']+508:raise ValueError('actual indexed row transport')
reference=W/'mac-value-comparison106-numeric-source03/template.lean';t=reference.read_text();start=t.index('theorem semantic');end=t.index('end ShielddSecurity',start);body=t[start:end]
body=body.replace('theorem semantic','theorem selected_numeric').replace('(arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)','(selected : Satisfies rho CapturedValueComparison105.actualRows)').replace('have h:=CapturedValueComparison105.semantic rho one arithmetic','have h : eval rho [(470,-1),(32752,1),(copy,1)]=rawScan rho (eval rho CapturedValueComparison105.initial) CapturedValueComparison105.entries := by\n    rw [←CapturedValueComparison105.output_exact]\n    exact chain_sound rho CapturedValueComparison105.initial CapturedValueComparison105.entries one CapturedValueComparison105.production_checked selected')
header='import ShielddSecurity.CapturedValueComparison106\nimport ShielddSecurity.CompilerColumnRenaming05\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.AssetComparison110\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101 BinaryComparison100 CapturedValueComparison106\nvariable {F : Type} [Field F] [CharP F p]\n'
(S/'numeric-template.lean').write_text(header+body+'end ShielddSecurity.AssetComparison110\n')
(S/'rename-template.lean').write_text('import ShielddSecurity.CompilerColumnRenaming05\nimport ShielddSecurity.CapturedValueComparison105\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnamespace ShielddSecurity.AssetComparison110\ndef rename (column : Nat) : Nat :=\n  if 216≤column ∧ column<471 then column+255\n  else if 32246≤column ∧ column<32754 then column+508 else column\ntheorem copy_fixed : rename CompilerArithmeticTransport41.copy=CompilerArithmeticTransport41.copy := by decide\nend ShielddSecurity.AssetComparison110\n')
(S/'source-binding01.json').write_text(json.dumps({'old':pin(old),'target':pin(new),'numeric_template':pin(reference),'every_entry':254,'every_row':508,'scope':'Exact DATA row/port transport; kernel declarations remain unqualified.'},sort_keys=True)+'\n')
(S/'generate.py').write_text('''from pathlib import Path
import sys,re,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\\n')
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'sealed refresh refusal')
binding=json.loads((S/'source-binding01.json').read_bytes())
for key in ['old','target','numeric_template']:require(pin(Path(binding[key]['path']))==binding[key],'exact source inputs before emission')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);outputs=[]
def emit(name,t,audits):
 require(len(t.encode())<=262144,'finite source')
 t+='\\n'+''.join('set_option pp.all true in\\n#check @'+n+'\\n#print axioms '+n+'\\n'for n in audits)
 p=r/(name+'.lean');p.write_text(t);outputs.append(dict(name=name,source=pin(p),audits=audits))
emit('AssetComparison110Rename',(S/'rename-template.lean').read_text(),['ShielddSecurity.AssetComparison110.rename','ShielddSecurity.AssetComparison110.copy_fixed'])
emit('AssetComparison110Numeric',(S/'numeric-template.lean').read_text(),['ShielddSecurity.AssetComparison110.selected_numeric'])
for j in range(8):
 old='CapturedValueComparison102Pilot'if j==0 else f'CapturedValueComparison104C{j:02d}'
 name=f'AssetComparison110Rows{j:02d}';length=60 if j==7 else64;start=10016+64*j
 t=f\"\"\"import ShielddSecurity.AssetComparison110Rename
import ShielddSecurity.{old}
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullArithmetic52
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
noncomputable def actualRows : List Row := CompilerColumnRenaming05.rows AssetComparison110.rename {old}.actualRows
theorem rows_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} {length} actualRows=true := by decide +kernel
theorem selected_satisfies {{F : Type}} [Field F] (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : Satisfies rho actualRows :=
  CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} {length} actualRows rows_checked (by decide) rho arithmetic
end ShielddSecurity.{name}
\"\"\"
 emit(name,t,['ShielddSecurity.'+name+'.'+n for n in ['actualRows','rows_checked','selected_satisfies']])
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),scope='Selected-value numeric bridge and8 exact asset row transports only; final canonical assertion/shared constructor separate.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(outputs=len(outputs),audits=sum(len(o['audits'])for o in outputs))))
''')
(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
