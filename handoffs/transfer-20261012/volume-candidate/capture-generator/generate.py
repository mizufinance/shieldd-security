from pathlib import Path
import argparse,json,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output;assert not out.exists();tmp=out.with_name(out.name+'.pending');tmp.mkdir();d=json.loads((root/'data.json').read_text())
lc=lambda xs:'['+','.join('('+str(i)+','+str(v)+')' for i,v in xs)+']'
s="""-- GENERATED. Do not hand edit.
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateCapture857
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt fieldBinary
"""
names=[]
for pos,row in d['rows'].items():
 n='row'+pos;s+=f'noncomputable def {n} : Row := ⟨{lc(row[0])},{lc(row[1])}⟩\n'
 s+=f'''theorem {n}_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+{pos}) 1 [{n}]=true := by
  have found : CapturedFullRelation58.rowAt (177954+{pos})=some {n} := by rfl
  change decide ((1:Nat)=1) && (decide (CapturedFullRelation58.rowAt (177954+{pos})=some {n}) && true)=true
  rw [found]
  decide +kernel
'''
 if pos=='8129':
  terms="[(4789,-1),(7741,-1)] ++ weighted (List.range' 8127 128) 1"
  premise="-rho 4789-rho 7741+fieldBinary ((List.range' 8127 128).map rho)=0"
 else:
  terms="weighted (List.range' 7999 128) 1 ++ scaleLinear (-1) (weighted (List.range' 8127 128) 1) ++ [(8255,2^128),(8256,-1)]"
  premise="fieldBinary ((List.range' 7999 128).map rho)-fieldBinary ((List.range' 8127 128).map rho)+(2:F)^128*rho 8255-rho 8256=0"
 s+=f"""theorem {n}_shape : canonical p {lc(row[0])}=canonical p ({terms}) := by decide +kernel
 theorem {n}_satisfies (rho : Nat → F) (meaning : {premise}) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos}+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [{n}] {n}_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  have value : eval rho {n}.a=0 := by
    change eval rho {lc(row[0])}=0
    rw [canonical_equal rho _ _ {n}_shape]
    simp only [eval_append,eval_scale,weighted_eval,Int.cast_one,Int.cast_neg,Int.cast_pow,Int.cast_ofNat,one_mul,neg_one_mul,eval,add_zero,neg_mul]
    simpa only [sub_eq_add_neg,add_assoc] using meaning
  change eval rho {n}.a*eval rho {n}.a=eval rho []
  simp only [value,mul_zero,eval]
"""
 names += [n+'_captured',n+'_shape',n+'_satisfies']
s+="""def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8129+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8261+i)) 1

theorem rows (rho : Nat → F)
    (candidate : -rho 4789-rho 7741+fieldBinary ((List.range' 8127 128).map rho)=0)
    (difference : fieldBinary ((List.range' 7999 128).map rho)-fieldBinary ((List.range' 8127 128).map rho)+(2:F)^128*rho 8255-rho 8256=0) : Rows rho :=
  ⟨row8129_satisfies rho candidate,row8261_satisfies rho difference⟩
end ShielddSecurity.VolumeCandidateCapture857
""";names+=['Rows','rows']
for name in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.VolumeCandidateCapture857.{name}\n#print axioms ShielddSecurity.VolumeCandidateCapture857.{name}\n'
import re
head=s[:s.index('noncomputable def row8129')]
first=s[s.index('noncomputable def row8129'):s.index('noncomputable def row8261')]
second=s[s.index('noncomputable def row8261'):s.index('def Rows')]
rootbody=s[s.index('def Rows'):s.index('end ShielddSecurity.VolumeCandidateCapture857')]
outputs={}
def emit(name,header,body):
 matches=list(re.finditer(r'(?m)^ ?theorem ([A-Za-z0-9_]+)',body));audits=[];text=header
 if matches:
  text+=body[:matches[0].start()]
  for i,m in enumerate(matches):
   text+=body[m.start():matches[i+1].start() if i+1<len(matches) else len(body)]
   n=m[1];audits.append(n);text+=f'\nset_option pp.all true in\n#check @ShielddSecurity.VolumeCandidateCapture857.{n}\n#print axioms ShielddSecurity.VolumeCandidateCapture857.{n}\n'
 else:text+=body
 text+='end ShielddSecurity.VolumeCandidateCapture857\n'
 p=tmp/'source-root/ShielddSecurity'/(name+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=audits)
emit('VolumeCandidateCapture857A',head,first)
emit('VolumeCandidateCapture857B',head,second)
header=head.replace('import ShielddSecurity.CompilerRowSlice63','import ShielddSecurity.VolumeCandidateCapture857A\nimport ShielddSecurity.VolumeCandidateCapture857B\nimport ShielddSecurity.CompilerRowSlice63')
emit('VolumeCandidateCapture857',header,rootbody)
(tmp/'generation.json').write_text(json.dumps(outputs)+'\n');os.replace(tmp,out)
