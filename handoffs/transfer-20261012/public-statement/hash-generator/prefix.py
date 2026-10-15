import gzip
from pathlib import Path
import json,hashlib,sys
S=Path(__file__).resolve().parent
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=False);root=out/'source-root/ShielddSecurity';root.mkdir(parents=True)
d=json.loads(gzip.decompress((S/'data.json.gz').read_bytes()));COPY=200692
lc=lambda x:'['+','.join('('+str(c)+','+str(v)+')'for c,v in x)+']'
arr=lambda x:'(Array.mk ['+','.join(x)+'])'
mods=[]
for a in [x for x in d['phases'] if x['round']<2]:
 name=f"PublicStatementHashCapture972C{a['call']}B{a['block']}R{a['round']:02d}";mods.append(name);w=a['width'];r=a['round'];param='TransferPoseidonCall04Shared01'if w==6 else'TransferPoseidonWidth3Call08Shared01'
 s=f'''import ShielddSecurity.AuthorizationPoseidonPhase517
import ShielddSecurity.{param}
-- Generated from exact captured rows; no semantic input assumptions.
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerIndexed01 Poseidon
open CapturedInitial73419Generic01 (p copy)
def parameters := {param}.parameters
'''
 for key in ['before','shifted','transformed','after']:
  s+=f'def {key} : State Linear {w} := fun i => {arr([lc(x)for x in a[key]])}.getD i.val []\n'
 s+='def rows : List Row := ['+','.join('⟨'+lc(x)+','+lc(y)+'⟩'for x,y in a['rows'])+']\n'
 s+=f'def data : AuthorizationPoseidonPhase517.Data {w} :=\n  ⟨parameters,{r},0,0,before,shifted,transformed,after,rows,\n'
 s+='    (fun i => '+arr(['none'if x is None else'some '+str(x)for x in a['pivots']])+').getD i.val none),\n' if False else ''
 s+='    (fun i => '+arr(['none'if x is None else'some '+str(x)for x in a['pivots']])+'.getD i.val none),\n'
 s+='    (fun i => '+arr(list(map(str,a['rowStarts'])))+'.getD i.val 0),\n'
 s+='    (fun i => '+arr(list(map(str,a['coefficients'])))+'.getD i.val 0)⟩\n'
 for i in range(w):s+=f'theorem column{i} : PoseidonIndexedFolded02.checkColumn p copy rows.toArray parameters {r} before shifted transformed (AuthorizationPoseidonPhase517.hints data) {i}=true := by decide +kernel\n'
 if r>=34:
  for j in range(w):s+=f'theorem mix{j} : decide (canonical p (after {j})=canonical p (mixLinear parameters.mds transformed {j}))=true := by decide +kernel\n'
 s+=f'''theorem checked : PoseidonIndexedFolded02.checkRound p copy rows.toArray parameters {r} before shifted transformed after (AuthorizationPoseidonPhase517.hints data)=true := by
  simp only [PoseidonIndexedFolded02.checkRound,Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro i _
    have cases : '''+' ∨ '.join(f'i={i}'for i in range(w))+''' := by have h := i.isLt;simp only [Fin.ext_iff];omega
    rcases cases with '''+'|'.join(['rfl']*w)+'\n'+''.join(f'    · exact column{i}\n'for i in range(w))+'''  · decide +kernel
'''
 if r>=34:
  oldmix='  · decide +kernel\n'
  newmix='  · apply List.all_eq_true.mpr\n    intro i _\n    have cases : '+' ∨ '.join(f'i={i}'for i in range(w))+' := by have h := i.isLt;simp only [Fin.ext_iff];omega\n    rcases cases with '+'|'.join(['rfl']*w)+'\n'+''.join(f'    · exact mix{i}\n'for i in range(w))
  assert oldmix in s
  s=s.replace(oldmix,newmix)
 s+='theorem copy_checked : checkRow p rows ⟨[(0,1),(copy,-1)],[]⟩=true := by decide +kernel\n'
 s+='def captureIndices : List Nat := ['+','.join(map(str,a['indices']))+']\n'
 s+=f'''theorem arbitrary_round {{F : Type}} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0=1) (sat : Satisfies rho rows) :
    (fun i => eval rho (after i))=Poseidon.round (castParameters parameters) {r}
      (fun i => eval rho (before i)) :=
  AuthorizationPoseidonPhase517.arbitrary_round data checked copy_checked rho one sat
end ShielddSecurity.{name}
'''
 for n in ['checked','copy_checked','arbitrary_round']:
  s+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (root/(name+'.lean')).write_text(s)
(root/'PublicStatementHashCapture972.lean').write_text(''.join('import ShielddSecurity.'+n+'\n'for n in mods)+'namespace ShielddSecurity.PublicStatementHashCapture972\ndef phaseCount : Nat := 72\nend ShielddSecurity.PublicStatementHashCapture972\nset_option pp.all true in\n#check @ShielddSecurity.PublicStatementHashCapture972.phaseCount\n#print axioms ShielddSecurity.PublicStatementHashCapture972.phaseCount\n')
(out/'generation.json').write_text(json.dumps({'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'data_sha256':hashlib.sha256(gzip.decompress((S/'data.json.gz').read_bytes())).hexdigest(),'modules':mods,'scope':'round syntax and soundness only; call/input joins remain open'},indent=2)+'\n')
print(json.dumps({'modules':len(mods)+1,'output':str(out)}))
