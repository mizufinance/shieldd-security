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
namespace ShielddSecurity.DetectionSelector626
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
''';names=[]
for axis,start,col,value,sink in [('x',11052,14,33790,17832230285398775523840151435063191920633280288053987250961356462684628833490),('y',11054,15,33792,52236742954115892447572473178524297982305297140137344394933767595493156073169)]:
 s+=f'def {axis}Rows : List Row := ['+','.join(row(data[str(i)]) for i in [start,start+1])+']\n'
 s+=f'''theorem {axis}_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} 2 {axis}Rows=true := by decide +kernel
theorem {axis}_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {value}=rho 10*(rho {col}-({sink}:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} 2 {axis}Rows {axis}_checked (by decide) rho arithmetic
  have result := checked_product_sound rho {axis}Rows [(10,1)] [(35,1),(copy,-{sink})]
    [({value},1)] [({value+1},1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
'''.replace('[(35,1),(copy,-',f'[({col},1),(copy,-')
 names.extend([axis+'_checked',axis+'_value'])
s+='end ShielddSecurity.DetectionSelector626\n'
for n in names:s+=f'set_option pp.all true in\n#check @ShielddSecurity.DetectionSelector626.{n}\n#print axioms ShielddSecurity.DetectionSelector626.{n}\n'
(dest/'DetectionSelector626.lean').write_text(s);print('generated exact detection-key selector source; kernel checks pending')
