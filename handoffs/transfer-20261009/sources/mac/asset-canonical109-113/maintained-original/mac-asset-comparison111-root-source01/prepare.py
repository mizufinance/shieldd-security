from pathlib import Path
import json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-asset-comparison111-root-source01'
if S.exists():raise ValueError('immutable source')
S.mkdir()
names=[f'AssetComparison110Rows{i:02d}'for i in range(8)]
old=['CapturedValueComparison102Pilot']+[f'CapturedValueComparison104C{i:02d}'for i in range(1,8)]
def append(xs):return xs[0]if len(xs)==1 else xs[0]+'++('+append(xs[1:])+')'
t='import ShielddSecurity.AssetComparison110Numeric\n'+''.join('import ShielddSecurity.'+n+'\n'for n in names)+'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AssetComparison111
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F]
private theorem sat_append (rho : Nat → F) (left right : List Row)
    (a : Satisfies rho left) (b : Satisfies rho right) : Satisfies rho (left++right) := by
  intro row member
  rcases List.mem_append.mp member with member|member
  · exact a row member
  · exact b row member
theorem pullback_satisfies (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    Satisfies (fun column => rho (AssetComparison110.rename column)) CapturedValueComparison105.actualRows := by
  apply (CompilerColumnRenaming05.satisfies_rows AssetComparison110.rename rho CapturedValueComparison105.actualRows).mp
'''
t+='  change Satisfies rho (CompilerColumnRenaming05.rows AssetComparison110.rename ('+append([n+'.actualRows'for n in old])+'))\n'
t+='  simp only [CompilerColumnRenaming05.rows,List.map_append]\n'
t+='  change Satisfies rho ('+append([n+'.actualRows'for n in names])+')\n'
for n in names[:-1]:t+='  apply sat_append\n  · exact '+n+'.selected_satisfies rho arithmetic\n'
t+='  exact '+names[-1]+'.selected_satisfies rho arithmetic\n'
t+='''variable [CharP F p]
theorem canonical_value (rho : Nat → F) (n : Nat) (bound : n<p) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<255,rho (471+index)=BinaryComparison100.bit (F:=F)
      (CapturedValueComparison106.bitAt n (216+index))) : 1-rho 725+rho 33260=1 := by
  have seed : ∀ index<255,(fun column => rho (AssetComparison110.rename column)) (216+index)=
      BinaryComparison100.bit (F:=F) (CapturedValueComparison106.bitAt n (216+index)) := by
    intro index before
    have renamed : AssetComparison110.rename (216+index)=471+index := by
      unfold AssetComparison110.rename
      rw [if_pos (show 216≤216+index ∧ 216+index<471 by omega)]
      omega
    change rho (AssetComparison110.rename (216+index))=_
    rw [renamed]
    exact values index before
  have linked : (fun column => rho (AssetComparison110.rename column)) copy=1 := by
    simpa only [AssetComparison110.copy_fixed] using one
  have result:=AssetComparison110.selected_numeric (fun column => rho (AssetComparison110.rename column)) n bound linked
    (pullback_satisfies rho arithmetic) seed
  have last : AssetComparison110.rename 470=725 := by decide
  have pivot : AssetComparison110.rename 32752=33260 := by decide
  simpa only [last,pivot] using result
end ShielddSecurity.AssetComparison111
'''
(S/'template.lean').write_text(t)
g='''from pathlib import Path
import sys,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);t=(S/'template.lean').read_text();audits=['ShielddSecurity.AssetComparison111.pullback_satisfies','ShielddSecurity.AssetComparison111.canonical_value']
t+='\\n'+''.join('set_option pp.all true in\\n#check @'+n+'\\n#print axioms '+n+'\\n'for n in audits);require(len(t.encode())<=262144,'finite source');p=r/'AssetComparison111.lean';p.write_text(t)
put('generation01.json',dict(outputs=[dict(name='AssetComparison111',source=pin(p),audits=audits)],generator=pin(Path(__file__)),template=pin(S/'template.lean'),scope='Only actual asset508 arithmetic row transport and independent numeric canonical conclusion; no canonical assertion/shared constructor claimed.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(source=pin(p),audits=len(audits))))
'''
(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
