from pathlib import Path
import argparse,json,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
assert not args.output.exists();pending=args.output.with_name(args.output.name+'.pending');assert not pending.exists()
dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
d=json.loads((root/'data.json').read_text());assert d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert d['spool']['sha256']=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9'
assert len(d['assertions'])==1 and d['assertions'][0]['position']==22812
r=d['assertions'][0]['row'];lc=lambda xs:'['+','.join(f'({c},{v})' for c,v in xs)+']'
assert r[1]==[]
s='''-- GENERATED from the maintained exact public-statement capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.PublicStatementHash977C187
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementCapture997
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {F : Type} [Field F] [CharP F p]
'''
s+='noncomputable def row : Row := ⟨'+lc(r[0])+',[]⟩\n'
s+='''theorem row_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+22812) 1 [row]=true := by decide +kernel

theorem row_shape : canonical p row.a=canonical p (PublicStatementHash977C187.result++[(22737,-1)]) := by decide +kernel

theorem row_value (rho : Nat → F) : eval rho row.a=eval rho PublicStatementHash977C187.result-rho 22737 := by
  rw [canonical_equal rho _ _ row_shape,eval_append]
  simp only [eval,Int.cast_neg,Int.cast_one,neg_one_mul,add_zero,sub_eq_add_neg]

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22812+i)) 1

theorem rows (rho : Nat → F) (claimed : eval rho PublicStatementHash977C187.result=rho 22737) : Rows rho := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row] row_captured rho).mp
  intro selected member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst selected
  change eval rho row.a*eval rho row.a=eval rho []
  rw [row_value,claimed,sub_self]
  simp only [zero_mul,eval]
end ShielddSecurity.PublicStatementCapture997
'''
names=['row_captured','row_shape','row_value','Rows','rows']
for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.PublicStatementCapture997.{n}\n#print axioms ShielddSecurity.PublicStatementCapture997.{n}\n'
f=dst/'PublicStatementCapture997.lean';f.write_text(s)
(pending/'generation.json').write_text(json.dumps({'PublicStatementCapture997':dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=names)},indent=2)+'\n')
os.replace(pending,args.output);print(json.dumps(dict(modules=1,audits=len(names))))
