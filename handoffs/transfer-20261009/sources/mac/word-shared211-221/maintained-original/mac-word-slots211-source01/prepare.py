from pathlib import Path
import sys,json,hashlib,zlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-word-slots211-source01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(b):
 def pairs(xs):
  out={}
  for k,v in xs:require(k not in out,'duplicate JSON');out[k]=v
  return out
 require(b.endswith(b'\n')and b.count(b'\n')==1,'one framed JSON line')
 return json.loads(b,object_pairs_hook=pairs)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated SOURCE flags')
require(not S.exists(),'immutable SOURCE namespace')
qp=W/'mac-assertion-provider50-source01/qualification01.json';q=strict(qp.read_bytes())
require(q['runtime']=='844389ee069e1fb2e576708842d0b389b4d9a44a'and q['source_context']=='cec1b30defc23497c8e9b30528dca12b09d328ea','exact runtime/source context')
pins={str(qp):pin(qp)};coeff=[]
for key in ['old_coefficients','extra_coefficients']:
 p=Path(q[key]['path']);require(pin(p)==q[key],'coefficient SHA before read');pins[str(p)]=q[key]
 v=strict(p.read_bytes())
 if key=='extra_coefficients':require(v['first_index']==len(coeff),'coefficient origin index')
 coeff+=v['coefficients']
records=[]
for chunk in q['chunks']:
 p=Path(chunk['data']['path']);require(pin(p)==chunk['data'],'compressed exact SHA before decode');pins[str(p)]=chunk['data']
 d=zlib.decompressobj();b=d.decompress(p.read_bytes(),1048577)
 require(len(b)<=1048576 and d.eof and not d.unused_data and not d.unconsumed_tail,'bounded zlib exact EOF no trailing')
 require(len(b)==chunk['decoded_bytes']and hashlib.sha256(b).hexdigest()==chunk['decoded_sha256'],'decoded exact capture DATA')
 v=strict(b);require(v['count']==chunk['count']==len(v['records']) and v['start']==chunk['start'],'chunk framing')
 records+=v['records']
require(len(records)==22816 and [r['index']for r in records]==list(range(177954,200770)),'complete indexed assertion inventory')
booleans={}
for r in records:
 x=r.get('x',[])
 if r.get('constructor')=='squareLinear'and x==r['y']and len(x)==1 and coeff[x[0][1]]==1 and 3<=x[0][0]<22738:
  require(r['actual']==[x,x]and x[0][0]not in booleans,'exact distinct original Boolean row')
  booleans[x[0][0]]=r['assertion']
require(len(booleans)==10783,'complete Boolean original inventory')
selected=[];excluded=[]
for r in records:
 if r.get('constructor')!='linear':continue
 x=r['x'];y=r['y']
 if not x or len(y)!=1 or coeff[y[0][1]]!=1:continue
 start=x[0][0];width=len(x);value=y[0][0]
 if not(3<=start and start+width<=22738 and 3<=value<22738):continue
 if [(col,coeff[c])for col,c in x]!=[(start+i,2**i)for i in range(width)]:continue
 if not all(start+i in booleans for i in range(width)):
  excluded.append(dict(position=r['assertion'],start=start,width=width,value=value,reason='one or more columns lack wire-Boolean recipe'));continue
 first=booleans[start]
 require([booleans[start+i]for i in range(width)]==list(range(first,first+width)),'actual consecutive Boolean recipes')
 require(first+width<=22816 and(value<start or start+width<=value),'position bound and value outside seeded bit window')
 require(r['index']==177954+r['assertion'],'exact captured reconstruction position')
 selected.append(dict(position=r['assertion'],start=start,width=width,value=value,first=first,index=r['index'],outlined_recipe_x=x,outlined_recipe_y=y,actual=r['actual']))
require(len(selected)==66 and len(excluded)==21,'complete exact weighted word classification')
modules={}
for block in range((len(selected)+3)//4):
 n='CapturedWordSlots211B'+str(block).zfill(3)
 body='''import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.'''+n+'''
open WordHints210 CompilerAssertionBlock51 CompilerArithmeticTransport41
'''
 names=[]
 for j,r in enumerate(selected[block*4:block*4+4]):
  ns='W'+str(block*4+j).zfill(2)
  body+='namespace '+ns+'\n'
  body+=f'''def slot : Slot := ⟨{r['position']},{r['start']},{r['width']},{r['value']}⟩
def first : Nat := {r['first']}
theorem checked : checkSlot CapturedFullAssertions54.recipeAt slot=true := by decide
theorem bits_checked : BooleanHints207.checkSlots CapturedFullAssertions54.recipeAt (bitSlots slot first)=true := by decide
theorem positions : slot.position<22816 ∧ first+slot.width≤22816 := by decide
theorem originals : (3≤slot.start ∧ slot.start+slot.width≤22738) ∧ (3≤slot.value ∧ slot.value<22738) := by decide
theorem outside : slot.value<slot.start ∨ slot.start+slot.width≤slot.value := by decide
variable {{F : Type}} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (n : Nat)
 (bound : n<2^{r['width']}) (meaning : base {r['value']}=(n : F)) :
 ∃ row,CapturedFullRelation58.rowAt {r['index']}=some row ∧
 Square (eval (CapturedFullRelation58.candidate (completed base slot n)) row.a)
        (eval (CapturedFullRelation58.candidate (completed base slot n)) row.b) :=
 selected_complete base slot n bound meaning outside originals.1 originals.2 positions.1 checked
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∃ n : Nat,n<2^{r['width']} ∧ (n : F)=rho {r['value']} :=
 WordHints210.sound rho satisfied slot positions.1 checked (bitSlots slot first)
   bits_checked (bit_positions slot first positions.2) (bit_coverage slot first)
end {ns}
'''
  names += [ns+'.'+s for s in ['slot','first','checked','bits_checked','positions','originals','outside','constructor','sound']]
 body+='end ShielddSecurity.'+n+'\n'
 modules[n]=dict(body=body,names=names)
inputs=[W/'mac-word-hints210-source03/source-root/ShielddSecurity/WordHints210.lean',W/'mac-boolean-hints207-source05/source-root/ShielddSecurity/BooleanHints207.lean']
for p in inputs:pins[str(p)]=pin(p)
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-word-hints210-source03/generate.py').read_bytes())
data=dict(selected=selected,excluded=excluded,qualification=pin(qp),runtime=q['runtime'],source_context=q['source_context'],scope='SOURCE/DATA only, exact weighted recipe and original Boolean-port classification. No kernel or legal-input truth credit.')
(S/'selected-data01.json').write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n');pins[str(S/'selected-data01.json')]=pin(S/'selected-data01.json')
(S/'templates01.json').write_text(json.dumps(dict(modules=modules,inputs=pins,scope='SOURCE_ONLY_UNRUN 66 actual reconstruction rows, 17 compact groups, 594 planned full signature/standard axiom observations. Full captured relation gives bounded natural meanings. Independent per-word constructor assumes only bounded n and original input value meaning. No desired row/hash truth premise. Constructors are separate assignments; simultaneous overlap/role consistency, shifted flag7607, fresh comparator51208, remaining assertions/full legal witness/native stay OPEN.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(stage=str(S),words=len(selected),modules=len(modules),planned_audits=66*9,excluded=len(excluded))))
