from pathlib import Path
import json,sys
root=Path(__file__).resolve().parent;out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=False);dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True);data=json.loads((root/'rows.json').read_text())
def lc(t):return '['+','.join(f'({c},{v})' for c,v in t)+']'
def row(r):return '⟨'+lc(r[0])+','+lc(r[1])+'⟩'
s='''-- GENERATED from rows.json. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierSelectors631
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
'''
px=49822839976625491399435002605169580882773999909559575334089637637825427273330;py=29108985603249989484651727880329493522712908252517904247459350893053326313050
dx=17832230285398775523840151435063191920633280288053987250961356462684628833490;dy=52236742954115892447572473178524297982305297140137344394933767595493156073169
entries=[('payloadX',98828,10,[(35,1),(200692,-px)]),('payloadY',98830,10,[(36,1),(200692,-py)])]
for family,start in [(0,119574),(2,131648),(3,138941),(4,146234)]:
 entries += [(f'family{family}X',start,108486,[(33790,1),(121566,-1),(200692,f'({dx}:Int)-{px}')]),(f'family{family}Y',start+2,108486,[(33792,1),(121568,-1),(200692,f'({dy}:Int)-{py}')])]
names=[]
for name,start,flag,terms in entries:
 value=data[str(start+1)][1][0][0];assert value==start+22738
 s+=f'def {name}Rows : List Row := ['+','.join(row(data[str(i)]) for i in [start,start+1])+']\n'
 s+=f'''theorem {name}_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} 2 {name}Rows=true := by decide +kernel
theorem {name}_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {value}=rho {flag}*eval rho {lc(terms)} := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} 2 {name}Rows {name}_checked (by decide) rho arithmetic
  have result := checked_product_sound rho {name}Rows [({flag},1)] {lc(terms)}
    [({value},1)] [({value+1},1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
'''
 names += [name+'_checked',name+'_value']
s+='end ShielddSecurity.TierSelectors631\n'
for n in names:s+=f'set_option pp.all true in\n#check @ShielddSecurity.TierSelectors631.{n}\n#print axioms ShielddSecurity.TierSelectors631.{n}\n'
(dest/'TierSelectors631.lean').write_text(s);print('generated exact 20-row tier selector source; kernel checks pending')
