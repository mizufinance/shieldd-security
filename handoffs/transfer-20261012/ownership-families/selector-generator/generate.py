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
namespace ShielddSecurity.CheckingSelector597
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
''';names=[]
for axis,start,col,value,sink in [('x',98832,42,121570,49822839976625491399435002605169580882773999909559575334089637637825427273330),('y',98834,43,121572,29108985603249989484651727880329493522712908252517904247459350893053326313050)]:
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
s+='end ShielddSecurity.CheckingSelector597\n'
for n in names:s+=f'set_option pp.all true in\n#check @ShielddSecurity.CheckingSelector597.{n}\n#print axioms ShielddSecurity.CheckingSelector597.{n}\n'
(dest/'CheckingSelector597.lean').write_text(s);print('generated exact checking-key selector source; kernel checks pending')
