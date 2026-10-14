from pathlib import Path
import argparse,json,hashlib,os,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output;assert not out.exists();tmp=out.with_name(out.name+'.pending');tmp.mkdir();d=json.loads((root/'data.json').read_text());assert d['position']==19539
lc=lambda xs:'['+','.join('('+str(i)+','+str(v)+')' for i,v in xs)+']'
s="""-- GENERATED. Edit maintained generator.
import ShielddSecurity.RoutingParameterHash878
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterCapture880
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
"""
s+='noncomputable def row : Row := ⟨'+lc(d['row'][0])+','+lc(d['row'][1])+'⟩\n'
s+="""theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+19539) 1 [row]=true := by decide +kernel
theorem shape : canonical p row.a=canonical p (RoutingParameterHash878.result++[(19589,-1)]) := by decide +kernel
def Rows (rho : Nat → F) : Prop := SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19539+i)) 1
theorem rows (rho : Nat → F) (meaning : eval rho RoutingParameterHash878.result=rho 19589) : Rows rho := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row] captured rho).mp
  intro selected member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst selected
  have value : eval rho row.a=0 := by
    rw [canonical_equal rho _ _ shape,eval_append,meaning]
    simp [eval]
  change eval rho row.a*eval rho row.a=eval rho []
  simp only [value,mul_zero,eval]
end ShielddSecurity.RoutingParameterCapture880
"""
for n in ['captured','shape','Rows','rows']:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.RoutingParameterCapture880.{n}\n#print axioms ShielddSecurity.RoutingParameterCapture880.{n}\n'
p=tmp/'source-root/ShielddSecurity/RoutingParameterCapture880.lean';p.parent.mkdir(parents=True);p.write_text(s)
(tmp/'generation.json').write_text(json.dumps({p.stem:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=re.findall(r'^#check @([A-Za-z0-9_.]+)',s,re.M))},indent=2)+'\n');os.replace(tmp,out)
