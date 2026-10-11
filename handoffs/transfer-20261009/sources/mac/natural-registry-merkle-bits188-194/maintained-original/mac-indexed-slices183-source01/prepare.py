from pathlib import Path
import json,hashlib,ast,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(ok,msg):
 if not ok:raise ValueError(msg)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparer')
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
roots=[W/'mac-indexed-slices183-source01',W/'mac-merkle-global-arithmetic184-source01',W/'mac-merkle-global-level185-source01']
require(all(not p.exists()for p in roots),'new immutable source stages')
require(__import__('shutil').disk_usage(W).free>=2147483648+8388608,'disk floor + finite source reserve')
g=r'''from pathlib import Path
import sys,json,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'source-root').exists()and not(S/'producer-manifest01.json').exists(),'immutable generation')
spec=json.loads((S/'templates01.json').read_bytes())
for p,v in spec['inputs'].items():require(pin(Path(p))==v,'exact source input '+p)
outputs=[]
for module,d in spec['modules'].items():
 names=['ShielddSecurity.'+module+'.'+n for n in d['names']]
 text=d['body']+'\n'+''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)
 require(len(text.encode())<=262144 and text.count('set_option maxHeartbeats 900000')==1 and text.count('set_option maxRecDepth 8192')==1,'bounded source')
 p=S/('source-root/ShielddSecurity/'+module+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x')as f:f.write(text)
 outputs.append(dict(name=module,source=pin(p),audits=names))
put('generation01.json',dict(outputs=outputs,generator=pin(Path(__file__)),templates=pin(S/'templates01.json'),scope=spec['scope'],inputs=spec['inputs']))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()})
put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')))
put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(modules=len(outputs),source_bytes=sum(o['source']['bytes']for o in outputs))))
'''
ast.parse(g)
header='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n'
helper='CompilerIndexedSlices183'
hb='''import ShielddSecurity.CompilerSelectedChunks172
import ShielddSecurity.CompilerSegmentChain33
'''+header+'''namespace ShielddSecurity.CompilerIndexedSlices183
open Compiler CompilerSelectedChunks172
def slicesAt (rows : List Row) (offset : Nat) : List Nat → List (List Row)
 | [] => []
 | width::widths => (rows.drop offset).take width :: slicesAt rows (offset+width) widths
theorem slicesAt_eq (rows : List Row) (offset : Nat) (widths : List Nat) :
 slicesAt rows offset widths=slices (rows.drop offset) widths := by
 induction widths generalizing offset with
 | nil => rfl
 | cons width widths ih => rw [slicesAt,slices,ih,List.drop_drop]
theorem partition (rows : List Row) (widths : List Nat) (enough : rows.length≤widths.sum) :
 (slicesAt rows 0 widths).flatten=rows := by
 rw [slicesAt_eq,List.drop_zero,slices_flatten,List.take_of_length_le enough]
variable {F : Type} [Field F]
theorem sound (rows : List Row) (widths : List Nat) (enough : rows.length≤widths.sum)
 (rho : Nat → F) (sat : AllSatisfied rho (slicesAt rows 0 widths)) : Satisfies rho rows := by
 rw [←partition rows widths enough]
 exact flatten_sound rho _ sat
theorem chain_sound (copy : Nat) (piece : Nat → CompilerSegmentCompletion11.Segment F copy)
 (count : Nat) (rho : Nat → F) (sat : ∀ i<count,Satisfies rho (piece i).rows) :
 Satisfies rho (CompilerSegmentChain33.rows copy piece count) := by
 induction count with
 | zero => intro row member;cases member
 | succ count ih =>
   intro row member
   rcases List.mem_append.mp member with member|member
   · exact ih (fun i less => sat i (by omega)) row member
   · exact sat count (by omega) row member
end ShielddSecurity.CompilerIndexedSlices183
'''
inputs={}
for p in [W/'mac-selected-chunks172-source03/source-root/ShielddSecurity/CompilerSelectedChunks172.lean',W/'mac-segment-chain33-source02/source-root/ShielddSecurity/CompilerSegmentChain33.lean',W/'mac-merkle-global-body181-source02/source-root/ShielddSecurity/MerkleGlobalBody181.lean',W/'mac-merkle-global-pilot182-source02/source-root/ShielddSecurity/CapturedMerkleGlobalPilot182.lean']:
 inputs[str(p)]=pin(p)
mods0={helper:dict(body=hb,names=['slicesAt','slicesAt_eq','partition','sound','chain_sound'])}
mods1={};mods2={};levelnames=[]
for level in range(15):
 leafnames=[]
 for block,offset in enumerate(range(0,424,16)):
  if level==0 and offset==0:
   leafnames.append('CapturedMerkleGlobalPilot182');continue
  module='CapturedMerkleGlobalArithmetic184L'+f'{level:02d}'+'B'+f'{block:02d}';leafnames.append(module);size=min(16,424-offset)
  body='import ShielddSecurity.MerkleGlobalBody181\n'+header+'namespace ShielddSecurity.'+module+'\n'+'''open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
'''+f'''def rows : List Row := (MerkleGlobalBody181.arithmeticRows {level}).drop {offset} |>.take {size}
def indices : List Nat := List.range' {3146+424*level+offset} {size}
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length={size} := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho rows := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.{module}
'''
  mods1[module]=dict(body=body,names=['rows','indices','productionCheck','checked','count','sound'])
 module='CapturedMerkleGlobalLevel185L'+f'{level:02d}';levelnames.append(module)
 widths='['+','.join(map(str,[16]*26+[8]))+']'
 body=''.join('import ShielddSecurity.'+n+'\n'for n in leafnames)+f'import ShielddSecurity.{helper}\n'+header+'namespace ShielddSecurity.'+module+'\n'+'''open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
'''+f'''theorem arithmetic_count : (MerkleGlobalBody181.arithmeticRows {level}).length=424 := by
 have selection := (MerkleFamily32Selection.counts {level}).2
 have phase0 : (MerkleGlobalBody181.phase0Rows {level}).length=17 := by rfl
 have phase1 : (MerkleGlobalBody181.phase1Rows {level}).length=25 := by rfl
 have tail : (MerkleGlobalBody181.tailRows {level}).length=373 := by
   simpa only [MerkleGlobalBody181.tailRows,CompilerColumnRenaming05.rows,List.length_map] using R22.counts.2.1
 simp only [MerkleGlobalBody181.arithmeticRows,MerkleGlobalBody181.selectionRows,List.length_append,List.length_take]
 rw [selection,phase0,phase1,tail]
 rfl
def chunks : List (List Row) := slicesAt (MerkleGlobalBody181.arithmeticRows {level}) 0 {widths}
theorem partition : chunks.flatten=MerkleGlobalBody181.arithmeticRows {level} := by
 apply CompilerIndexedSlices183.partition
 rw [arithmetic_count]
 decide
theorem copy_checked : MerkleGlobalBody181.copyCheck {level}=true := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleGlobalBody181.arithmeticRows {level}) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [{','.join(n+'.rows'for n in leafnames)}]
 exact {''.join('⟨'+n+'.sound rho satisfied,'for n in leafnames)+'True.intro'+'⟩'*len(leafnames)}
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) {level}) :=
 MerkleGlobalBody181.sound {level} copy_checked rho satisfied (arithmetic_sound rho satisfied)
end ShielddSecurity.{module}
'''
 mods2[module]=dict(body=body,names=['arithmetic_count','chunks','partition','copy_checked','arithmetic_sound','sound'])
module='CapturedMerkleGlobalLevels185'
body=''.join('import ShielddSecurity.'+n+'\n'for n in levelnames)+header+'namespace ShielddSecurity.'+module+'\n'+'''open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (i : Fin 15) :
 Satisfies rho (MerkleFamily32Whole.rows (F:=F) i) := by
 have cases : '''+' ∨ '.join('i='+str(i)for i in range(15))+''' := by
   have bound := i.isLt;simp only [Fin.ext_iff];omega
 rcases cases with '''+'|'.join(['rfl']*15)+'\n'+''.join(' · exact '+n+'.sound rho satisfied\n'for n in levelnames)+'end ShielddSecurity.'+module+'\n'
mods2[module]=dict(body=body,names=['sound'])
allmods=[mods0,mods1,mods2]
total=sum(len(json.dumps(m,separators=(',',':')).encode())for m in allmods)*2+len(g)*3
require(total<8388608,'source proposal finite physical bound')
for root,modules in zip(roots,allmods):
 root.mkdir();(root/'generate.py').write_text(g)
 with(root/'templates01.json').open('x')as f:f.write(json.dumps(dict(modules=modules,inputs=inputs,scope='SOURCE-only exact indexed row transport; all new audits UNRUN. No legal-input, desired-hash or initial row-truth premise. Historical captures and qualified template references retained; final native/full Transfer OPEN.'),sort_keys=True,separators=(',',':'))+'\n')
 (root/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(dict(roots=list(map(str,roots)),modules=list(map(len,allmods)),preflight_source_bytes=total)))
