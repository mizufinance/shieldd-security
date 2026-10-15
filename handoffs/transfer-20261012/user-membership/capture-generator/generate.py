from pathlib import Path
import json,argparse,hashlib,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
data=json.loads((root/'data.json').read_text());assert [d['position'] for d in data['assertions']]==[1524,1779];assert [e['name'] for e in data['entries']]==['sender','receiver']
lc=lambda terms:'['+','.join('('+str(c)+','+str(v)+')' for c,v in terms)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def product(d):return '⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩'
name='UserPathCapture968';s='''-- GENERATED from maintained exact user-membership capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.UserPathHash958C37
import ShielddSecurity.UserPathHash958C54
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathCapture968
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
''';names=[]
for e,ci in zip(data['entries'],[37,54]):
 n=e['name'];out=e['output'][0][0];s+=f'noncomputable def {n}Entry : Entry := '+product(e)+'\n'
 s+=f'''theorem {n}_checked : check {n}Entry=true := by decide +kernel
theorem {n}_shape : canonical p {n}Entry.right=canonical p (UserPathHash958C{ci}.result++[(5,-1)]) := by decide +kernel
theorem {n}_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {out}=rho 10*(eval rho UserPathHash958C{ci}.result-rho 5) := by
  have result := MapArithmeticAdapter704.equation {n}Entry {n}_checked rho arithmetic
  have output : eval rho {n}Entry.output=rho {out} := by simp [{n}Entry,eval]
  have square : {n}Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ {n}_shape,eval_append] at result
  simpa only [{n}Entry,eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_one_mul,sub_eq_add_neg] using result
''';names += [n+'_checked',n+'_shape',n+'_value']
for d in data['assertions']:
 pos=d['position'];out=d['output'];n='row'+str(pos);s+='noncomputable def '+n+' : Row := '+row(d['row'])+'\n'
 s+=f'''theorem {n}_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+{pos}) 1 [{n}]=true := by decide +kernel

theorem {n}_satisfies (rho : Nat → F) (zero : rho {out}=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos}+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [{n}] {n}_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho {lc(d['row'][0])}*eval rho {lc(d['row'][0])}=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
''';names += [n+'_captured',n+'_satisfies']
s+='''def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1524+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1779+i)) 1

theorem rows (rho : Nat → F) (sender : rho 41626=0) (receiver : rho 49580=0) : Rows rho :=
  ⟨row1524_satisfies rho sender,row1779_satisfies rho receiver⟩
''';names+=['Rows','rows'];s+='end ShielddSecurity.'+name+'\n'
for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
f=dst/(name+'.lean');f.write_text(s)
(pending/'generation.json').write_text(json.dumps({name:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=names)},indent=2)+'\n');os.replace(pending,a.output);print(json.dumps(dict(modules=1,audits=len(names))))
