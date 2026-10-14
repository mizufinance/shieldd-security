from pathlib import Path
import json,argparse,hashlib,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
data=json.loads((root/'data.json').read_text());assert [d['position'] for d in data['assertions']]==[7611,8262]
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
signed=lambda xs:[[c,v if v<p//2 else v-p] for c,v in xs]
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def product(d):return '⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩'
name='VolumeBoundaryCapture843';s='''import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeBoundaryCapture843
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
''';names=[]
for e in data['entries']:
 n=e['name'];out=e['output'][0][0];left=lc(signed(e['left']));right=lc(signed(e['right']));s+='noncomputable def '+n+'Entry : Entry := '+product(e)+'\n'
 s+=f'''theorem {n}_checked : check {n}Entry=true := by decide +kernel
theorem {n}_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {out}=eval rho {left}*eval rho {right} := by
  have result := MapArithmeticAdapter704.equation {n}Entry {n}_checked rho arithmetic
  have left : canonical p {lc(e['left'])}=canonical p {left} := by decide +kernel
  have right : canonical p {lc(e['right'])}=canonical p {right} := by decide +kernel
  simp only [{n}Entry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
''';names += [n+'_checked',n+'_equation']
for d in data['assertions']:
 pos=d['position'];out=d['output'];n='row'+str(pos);s+='noncomputable def '+n+' : Row := '+row(d['row'])+'\n'
 s+=f"theorem {n}_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+{pos}) 1 [{n}]=true := by decide +kernel\n"
 premise=f"(zero : rho {out}=0)" if pos==8262 else f"(equal : rho 7739=rho {out})"
 s+=f"""
theorem {n}_satisfies (rho : Nat → F) {premise} :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos}+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [{n}] {n}_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho {lc(d['row'][0])}*eval rho {lc(d['row'][0])}=eval rho []
"""
 if pos==8262:s+='  simp only [eval,zero,mul_zero,add_zero]\n'
 else:
  signedrow=lc(signed(d['row'][0]));s+=f"""  have shape : canonical p {lc(d['row'][0])}=canonical p {signedrow} := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,equal]
  ring
"""
 names += [n+'_captured',n+'_satisfies']
s+='''def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7611+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8262+i)) 1

theorem rows (rho : Nat → F) (day : rho 7739=rho 108480) (limit : rho 108908=0) : Rows rho :=
  ⟨row7611_satisfies rho day,row8262_satisfies rho limit⟩
''';names+=['Rows','rows'];s+='end ShielddSecurity.'+name+'\n'
for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
f=dst/(name+'.lean');f.write_text('-- GENERATED from maintained exact capture; do not edit.\n'+s)
(pending/'generation.json').write_text(json.dumps({name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))},indent=2)+'\n');os.replace(pending,a.output)
