from pathlib import Path
import sys,json,hashlib,zlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-boolean-slots208-source01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(b):
 def pairs(v):
  out={}
  for k,x in v:require(k not in out,'duplicate JSON');out[k]=x
  return out
 require(b.endswith(b'\n') and b.count(b'\n')==1,'single framed JSON line')
 return json.loads(b,object_pairs_hook=pairs)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
qpath=W/'mac-assertion-provider50-source01/qualification01.json';q=strict(qpath.read_bytes());require(q['runtime']=='844389ee069e1fb2e576708842d0b389b4d9a44a' and q['source_context']=='cec1b30defc23497c8e9b30528dca12b09d328ea','exact capture context')
pins={str(qpath):pin(qpath)};groups=[];excluded=[];seen=set()
for chunk in q['chunks']:
 p=Path(chunk['data']['path']);require(pin(p)==chunk['data'],'compressed payload exact SHA before decode');pins[str(p)]=chunk['data']
 d=zlib.decompressobj();b=d.decompress(p.read_bytes(),1048577);require(len(b)<=1048576 and d.eof and not d.unused_data and not d.unconsumed_tail,'bounded exact zlib EOF/no trailing');require(len(b)==chunk['decoded_bytes'] and hashlib.sha256(b).hexdigest()==chunk['decoded_sha256'],'exact decoded DATA')
 v=strict(b);require(v['count']==chunk['count'] and len(v['records'])==v['count'] and v['start']==chunk['start'],'exact block framing')
 slots=[]
 for r in v['records']:
  x=r.get('x',[])
  if r.get('constructor')=='squareLinear' and x==r['y'] and len(x)==1 and x[0][1]==0:
   col=x[0][0];require(r['actual']==[x,x] and r['index']==177954+r['assertion'],'exact one-coefficient Boolean actual row')
   require(col not in seen,'distinct Boolean column');seen.add(col)
   if 3<=col<22738:slots.append([r['index']-177954,col])
   else:excluded.append(dict(position=r['index'],column=col,left=r['left'],right=r['right']))
 if slots:groups.append(dict(block=chunk['index'],slots=slots,count=len(slots)))
require(sum(g['count']for g in groups)==10783 and excluded==[dict(position=180208,column=51208,left=[2,335369],right=[2,335368])],'complete exact original-column Boolean inventory; fresh comparator kept OPEN')
modules={}
for g in groups:
 n='CapturedBooleanSlots208B'+str(g['block']).zfill(4);literal='['+','.join('('+str(a)+','+str(b)+')'for a,b in g['slots'])+']'
 body=f'''import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{n}
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := {literal}
theorem count : slots.length={g['count']} := rfl
theorem checked : checkSlots CapturedFullAssertions54.recipeAt slots=true := by decide
theorem originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738 := by decide
theorem positions : ∀ slot∈slots,slot.1<22816 := by decide
variable {{F : Type}} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (coverage : ∀ slot∈slots,slot.2∈columns) : ∀ slot∈slots,
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.b) :=
 fun slot member => candidate_selected base bits columns slots checked originals coverage positions slot member
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∀ slot∈slots,rho slot.2=0 ∨ rho slot.2=1 := by
 intro slot member
 obtain ⟨outlined,matching⟩:=checked_slot _ slots checked slot member
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 slot.1
   (positions slot member) (outlined,wireRecipe slot.2) matching
 exact (wire_truth rho slot.2).mp truth
end ShielddSecurity.{n}
'''
 modules[n]=dict(body=body,names=['slots','count','checked','originals','positions','constructor','sound'])
for p in [W/'mac-boolean-hints207-source03/source-root/ShielddSecurity/BooleanHints207.lean',W/'mac-full-captured-relation58-source02/source-root/ShielddSecurity/CapturedFullRelation58.lean']:pins[str(p)]=pin(p)
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'selected-data01.json').write_text(json.dumps(dict(groups=groups,excluded=excluded,count=10783,source=q['runtime'],qualification=pin(qpath),scope='Exact SOURCE/DATA selected original Boolean assertion slots. No fresh kernel credit; fresh comparator Boolean at180208 excluded.'),sort_keys=True,separators=(',',':'))+'\n')
pins[str(S/'selected-data01.json')]=pin(S/'selected-data01.json')
(S/'templates01.json').write_text(json.dumps(dict(modules=modules,inputs=pins,scope='SOURCE_ONLY_UNRUN. Exact checked recipe/position certificates for10783 original-column Boolean assertions. Bool seed constructor plus arbitrary full-relation Boolean recovery; selected hint/user columns may change, lawful word reconstruction/semantic frames/one fresh comparatorBoolean/all other assertions remain OPEN.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(modules=len(modules),slots=10783,planned_audits=7*len(modules),excluded=excluded)))
