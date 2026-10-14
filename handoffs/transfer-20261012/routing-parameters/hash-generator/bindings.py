from pathlib import Path
import json,sys
D=json.loads((Path(__file__).resolve().parent/'data.json').read_text());out=(Path(sys.argv[1])/'source-root/ShielddSecurity');out.mkdir(parents=True,exist_ok=True)
for a in [x for x in D['phases'] if x['round']<2]:
 ci,bi,r=a['call'],a['block'],a['round'];cnt=len(a['indices'])-1;start=a['indices'][0];w=a['width'];src=f'RoutingParameterHashCapture873C{ci}B{bi}R{r:02d}';name=f'RoutingParameterHashPrefix874C{ci}B{bi}R{r:02d}'
 s=f'''import ShielddSecurity.{src}
import ShielddSecurity.AuthorizationPoseidonRowBridge521
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def arithmeticRows := {src}.rows.take {cnt}
theorem actual : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} {cnt} arithmeticRows=true := by decide +kernel
theorem split : {src}.rows=arithmeticRows++[AuthorizationPoseidonRowBridge521.copyRow] := by decide +kernel
theorem arbitrary_round {{F : Type}} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0=1) (linked : rho copy=rho 0)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    (fun i => eval rho ({src}.after i))=Poseidon.round (Poseidon.castParameters {src}.parameters) {r}
      (fun i => eval rho ({src}.before i)) := by
  apply {src}.arbitrary_round rho one
  rw [split]
  exact AuthorizationPoseidonRowBridge521.from_arithmetic arithmeticRows {start} {cnt} actual (by decide) rho linked arithmetic
end ShielddSecurity.{name}
'''
 for n in ['actual','split','arbitrary_round']:s+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 (out/(name+'.lean')).write_text(s)
print('Prepared eight actual prefix row bindings')
