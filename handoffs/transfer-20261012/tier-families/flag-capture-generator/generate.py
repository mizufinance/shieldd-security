from pathlib import Path
import argparse, hashlib, json, os

root = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument('output', type=Path)
a = ap.parse_args()
assert not a.output.exists()
pending = a.output.with_name(a.output.name+'.pending')
dest = pending/'source-root/ShielddSecurity'
dest.mkdir(parents=True)
data = json.loads((root/'gates.json').read_text())
def lc(terms):
    return '['+','.join(f'({c},{v})' for c,v in terms)+']'
def row(value):
    return '⟨'+lc(value[0])+','+lc(value[1])+'⟩'
s = '''-- GENERATED from gates.json. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagCapture618
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
'''
names = []
for gate in data['gates']:
    name, start, value = gate['name'], gate['arithmeticStart'], gate['out']
    left, right = lc(gate['left']), lc(gate['right'])
    s += f'def {name}Rows : List Row := ['+','.join(map(row,gate['rows']))+']\n'
    s += f'''theorem {name}_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt {start} 2 {name}Rows=true := by decide +kernel
theorem {name}_value (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {value}=eval rho {left} * eval rho {right} := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 {start} 2 {name}Rows {name}_checked (by decide) rho arithmetic
  have result := checked_product_sound rho {name}Rows {left} {right}
    [({value},1)] [({value+1},1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
'''
    names += [name+'_checked',name+'_value']
s += '''theorem polynomial (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108486=(2*rho copy-rho 7607)*rho 10*
      (rho copy-rho 7597*rho 7599*rho 7601*rho 7603)*(rho copy-rho 7605) := by
  change rho 108486=(2*rho 200692-rho 7607)*rho 10*
    (rho 200692-rho 7597*rho 7599*rho 7601*rho 7603)*(rho 200692-rho 7605)
'''
for gate in reversed(data['gates']):
    s += f"  have {gate['name']} := {gate['name']}_value rho arithmetic\n"
s += '''  simp only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_mul] at same01 same012 same0123 regulatedExternal eligible flagged
  rw [flagged,eligible,regulatedExternal,same0123,same012,same01]
  ring
end ShielddSecurity.TierFlagCapture618
'''
names += ['polynomial']
for name in names:
    s += f'\nset_option pp.all true in\n#check @ShielddSecurity.TierFlagCapture618.{name}\n#print axioms ShielddSecurity.TierFlagCapture618.{name}\n'
p = dest/'TierFlagCapture618.lean'
p.write_text(s)
(pending/'generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=names,proof_credit=0),indent=2)+'\n')
os.replace(pending,a.output)
print('Generated six exact flag-product gates; kernel checks pending')
