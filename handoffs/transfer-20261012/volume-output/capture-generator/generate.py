from pathlib import Path
import json,argparse,hashlib,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
data=json.loads((root/'data.json').read_text());assert [d['position'] for d in data['assertions']]==[8316,8317]
lc=lambda xs:'['+','.join(f'({c},{v})' for c,v in xs)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def entry(d):return '⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩'
h=lambda ci:f'VolumeOutputHash918C{ci}.result'
v=lambda ci:'eval rho '+h(ci)
shapes={
'originSelect':('[(7606,1)]',h(149)+'++scaleLinear (-1) '+h(150),'rho 7606',v(149)+'-'+v(150)),
'nullifierSelect':('[(7605,1)]',h(150)+'++[(120324,1)]++scaleLinear (-1) '+h(152),'rho 7605',v(150)+'+rho 120324-'+v(152)),
'nullifier':('[(copy,2),(7607,-1)]',h(152)+'++[(121554,1)]','2*rho copy-rho 7607',v(152)+'+rho 121554'),
'commitmentSelect':('[(7605,1)]',h(151)+'++scaleLinear (-1) '+h(153),'rho 7605',v(151)+'-'+v(153)),
'commitment':('[(copy,2),(7607,-1)]',h(153)+'++[(121558,1)]','2*rho copy-rho 7607',v(153)+'+rho 121558')}
s="""-- GENERATED from maintained capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.VolumeOutputHashes919
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputCapture922
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
""";names=[]
for e in data['entries']:
 n=e['name'];out=e['output'][0][0];left,right,lv,rv=shapes[n];s+=f'noncomputable def {n}Entry : Entry := '+entry(e)+'\n'
 s+=f"""theorem {n}_checked : check {n}Entry=true := by decide +kernel
theorem {n}_left : canonical p {n}Entry.left=canonical p ({left}) := by decide +kernel
theorem {n}_right : canonical p {n}Entry.right=canonical p ({right}) := by decide +kernel
theorem {n}_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {out}=({lv})*({rv}) := by
  have result := MapArithmeticAdapter704.equation {n}Entry {n}_checked rho arithmetic
  have output : eval rho {n}Entry.output=rho {out} := by simp [{n}Entry,eval]
  have square : {n}Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ {n}_left,canonical_equal rho _ _ {n}_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
""";names += [n+'_checked',n+'_left',n+'_right',n+'_value']
for d in data['assertions']:
 pos=d['position'];col=d['column'];out=d['output'];n='row'+str(pos);s+=f'noncomputable def {n} : Row := '+row(d['row'])+'\n'
 s+=f"""theorem {n}_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+{pos}) 1 [{n}]=true := by decide +kernel
theorem {n}_shape : canonical p {n}.a=canonical p [({col},1),({out},-1)] := by decide +kernel
theorem {n}_satisfies (rho : Nat → F) (equal : rho {col}=rho {out}) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos}+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [{n}] {n}_captured rho).mp
  intro selected member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst selected
  have value : eval rho {n}.a=0 := by
    rw [canonical_equal rho _ _ {n}_shape]
    simp [eval,equal]
  change eval rho {n}.a*eval rho {n}.a=eval rho []
  simp only [value,mul_zero,eval]
""";names += [n+'_captured',n+'_shape',n+'_satisfies']
s+="""def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8316+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8317+i)) 1
 theorem rows (rho : Nat → F) (nullifier : rho 8509=rho 121556) (commitment : rho 8510=rho 121560) : Rows rho :=
  ⟨row8316_satisfies rho nullifier,row8317_satisfies rho commitment⟩
end ShielddSecurity.VolumeOutputCapture922
""";names+=['Rows','rows']
for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.VolumeOutputCapture922.{n}\n#print axioms ShielddSecurity.VolumeOutputCapture922.{n}\n'
f=dst/'VolumeOutputCapture922.lean';f.write_text(s);(pending/'generation.json').write_text(json.dumps({f.stem:dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))},indent=2)+'\n');os.replace(pending,a.output)
