from pathlib import Path
import json,sys,hashlib
root=Path(__file__).resolve().parent;out=Path(sys.argv[1]);out.mkdir();dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True);data=json.loads((root/'rows.json').read_text());assert data['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert data['capture_sha256']=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9'
def lc(t):return '['+','.join(f'({c},{v})' for c,v in t)+']'
def row(r):return '⟨'+lc(r[0])+','+lc(r[1])+'⟩'
s='''-- GENERATED from rows.json; do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignCapture654
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
'''
s+='noncomputable def productRows : List Row := ['+','.join(row(data['rows'][str(i)]) for i in [167507,167508])+']\n'
s+='noncomputable def assertionRows : List Row := ['+row(data['rows']['199867'])+']\n'
s+='''noncomputable def template : List Row :=
  [⟨subtract [(4281,1),(4534,1),(4789,-1),(6194,-1)] [(21712,1),(190245,1)],[]⟩]
theorem product_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 167507 2 productRows=true := by decide +kernel
theorem assertion_checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt 199867 1 assertionRows=true := by decide +kernel
theorem shape_checked : VariableOperationAdapter434.covers template assertionRows=true ∧
    VariableOperationAdapter434.covers assertionRows template=true := by constructor <;> decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem product (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 190245=rho 21711*(-2*rho 21712) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 167507 2 productRows product_checked (by decide) rho arithmetic
  have result := checked_product_sound rho productRows [(21711,1)] [(21712,-2)]
    [(190245,1)] [(190246,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero] using result

theorem rows_iff (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (199867+i)) 1 ↔
    rho 4281+rho 4534-rho 4789-rho 6194=(1-2*rho 21711)*rho 21712 := by
  have shapes : Satisfies rho assertionRows ↔ Satisfies rho template :=
    ⟨transfer rho _ _ shape_checked.1,
      transfer rho _ _ shape_checked.2⟩
  rw [←CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 199867 1 assertionRows assertion_checked rho,shapes]
  simp only [template,Satisfies,List.mem_singleton,forall_eq,VariableDoubleTemplate431.equality_row,
    eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul]
  rw [product rho arithmetic]
  ring_nf
end ShielddSecurity.BalanceSignCapture654
'''
names=['product_checked','assertion_checked','shape_checked','product','rows_iff']
for name in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.BalanceSignCapture654.{name}\n#print axioms ShielddSecurity.BalanceSignCapture654.{name}\n'
p=dest/'BalanceSignCapture654.lean';p.write_text(s);(out/'generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=names,proof_credit=0),indent=2)+'\n');print('Generated exact signed-balance product/assertion adapter; UNRUN')
