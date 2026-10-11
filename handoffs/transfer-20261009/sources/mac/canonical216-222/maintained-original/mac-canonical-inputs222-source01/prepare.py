from pathlib import Path
import json,hashlib,sys,os,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-canonical-comparisons216-source07';S=W/'mac-canonical-inputs222-source01'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated maintained preparation');require(not S.exists(),'fresh SOURCE namespace')
data=W/'mac-word-slots211-source01/selected-data01.json';dm=json.loads((data.parent/'producer-manifest01.json').read_bytes());require(pin(data)==dm['selected-data01.json'],'frozen exact weighted input DATA');selected=json.loads(data.read_bytes())['selected'];targets=[(i,v['value'])for i,v in enumerate(selected)if v['width']==255];require(len(targets)==14,'exact canonical255 records')
inputs={str(data):pin(data),str(P/'producer-manifest01.json'):pin(P/'producer-manifest01.json')};sources=[]
for i,value in targets:
 name='CapturedCanonical216W'+str(i).zfill(2);p=P/('source-root/ShielddSecurity/'+name+'.lean');require(pin(p)==json.loads((P/'generation01.json').read_bytes())['outputs'][[x['name']for x in json.loads((P/'generation01.json').read_bytes())['outputs']].index(name)]['source'],'frozen source root identity');require(re.search(r'\(n:F\)=rho '+str(value)+r'\s*:=',p.read_text()),'exact literal recovered input target');inputs[str(p)]=pin(p);sources.append(name)
body=''.join('import ShielddSecurity.'+n+'\n'for n in sources)+'''import ShielddSecurity.CanonicalRecovery195
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalInputs222
open CompilerAssertionBlock51 CompilerArithmeticTransport41
def columns : List Nat := '''+repr([value for _,value in targets]).replace(' ','')+'''
theorem count : columns.length=14 := rfl
variable {F : Type} [Field F] [CharP F p]
theorem recovered (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) : ∀ column∈columns,∃ n : Nat,n<p ∧ (n:F)=rho column := by
 simp only [columns,List.forall_mem_cons]
 exact '''
tail='by intro column member;cases member'
for name in reversed(sources):tail='⟨'+name+'.sound rho satisfied one,'+tail+'⟩'
body+=tail+'''
noncomputable def number (rho : Nat → F) (column : Nat) : Nat := by
 classical
 exact if h : ∃ n : Nat,n<p ∧ (n:F)=rho column then Classical.choose h else 0
theorem number_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) (column : Nat) (member : column∈columns) :
 number rho column<p ∧ (number rho column:F)=rho column := by
 have h:=recovered rho satisfied one column member
 simp only [number,dif_pos h]
 exact Classical.choose_spec h
theorem unique (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) (column : Nat) (member : column∈columns) (n : Nat)
 (bound : n<p) (meaning : (n:F)=rho column) : number rho column=n :=
 CapturedEpochHints62.cast_small_unique _ n (number_sound rho satisfied one column member).1 bound
 ((number_sound rho satisfied one column member).2.trans meaning.symm)
theorem representation_value (representation : PoseidonNatural192.CanonicalRepresentation F)
 (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (one : rho 0=1) (column : Nat) (member : column∈columns) :
 representation.value (rho column)=number rho column :=
 CanonicalRecovery195.value_unique representation _ _ (number_sound rho satisfied one column member).1
 (number_sound rho satisfied one column member).2
end ShielddSecurity.CanonicalInputs222
'''
names=['columns','count','recovered','number','number_sound','unique','representation_value'];st=os.statvfs(W);require(st.f_bavail*st.f_frsize>=2*1024**3+1048576,'SOURCE disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-shared-word-flags220-source04/generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(dict(modules={'CanonicalInputs222':dict(body=body,names=names)},inputs=inputs,scope='SOURCE_ONLY_UNRUN. Collects14 actual canonical255 input columns; full captured relation plus rho0=1 derives all natural bounds and casts, then a selected-column natural recovery function and uniqueness. Source roots not yet all qualified; exact topology must qualify each missing root first. Does not assume desired natural bounds or hash truth. CanonicalRepresentation remains explicit only in representation_value; no global field instance/native/full Transfer claimed.'),sort_keys=True,separators=(',',':'))+'\n')
