from pathlib import Path
import sys,json,hashlib,zlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-original-tag214-source03'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(b):
 def pairs(xs):
  d={}
  for k,v in xs:require(k not in d,'duplicate JSON');d[k]=v
  return d
 require(b.endswith(b'\n')and b.count(b'\n')==1,'one JSON line');return json.loads(b,object_pairs_hook=pairs)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated SOURCE flags');require(not S.exists(),'immutable SOURCE')
qp=W/'mac-assertion-provider50-source01/qualification01.json';q=strict(qp.read_bytes());require(q['runtime']=='844389ee069e1fb2e576708842d0b389b4d9a44a','exact runtime')
chunk=next(c for c in q['chunks']if c['start']<=185429<c['start']+c['count']);p=Path(chunk['data']['path']);require(pin(p)==chunk['data'],'compressed hash before decode')
d=zlib.decompressobj();b=d.decompress(p.read_bytes(),1048577);require(len(b)<=1048576 and d.eof and not d.unused_data and not d.unconsumed_tail,'bounded complete decode')
require(len(b)==chunk['decoded_bytes']and hashlib.sha256(b).hexdigest()==chunk['decoded_sha256'],'exact decoded DATA');v=strict(b);r=v['records'][185429-chunk['start']]
require(r['constructor']=='squareLinear'and r['x']==r['y']==[[0,7482],[7607,0]] and r['actual']==[[[7607,0],[200692,7482]],[[7607,0],[200692,7482]]]and r['assertion']==7475,'exact shifted square recipe/body/copy transport')
body='''import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedOriginalTag214
open CompilerAssertionBlock51 CompilerArithmeticTransport41
def recipe : Recipe := .square [(0,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7607,1)] [(0,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7607,1)]
theorem checked : CapturedFullAssertions54.recipeAt 7475=some (true,recipe) := rfl
variable {F : Type} [Field F]
theorem shifted_square (x zero : F) : Square (x-zero) (x-zero) ↔ x=zero ∨ x=zero+1 := by
 change (x-zero)*(x-zero)=x-zero ↔ _
 constructor
 · intro square
   have product : (x-zero)*((x-zero)-1)=0 := by rw [mul_sub,mul_one,square,sub_self]
   rcases mul_eq_zero.mp product with a | b
   · exact Or.inl (sub_eq_zero.mp a)
   · have equal : x=1+zero := sub_eq_iff_eq_add.mp (sub_eq_zero.mp b)
     exact Or.inr (by simpa only [add_comm] using equal)
 · rintro (rfl | rfl) <;> ring
noncomputable def seeded (base : Nat → F) (flag : Bool) : Nat → F :=
 fun column => if column=7607 then base 0+BooleanHints207.bitValue flag else base column
theorem seeded_outside (base : Nat → F) (flag : Bool) (column : Nat) (different : column≠7607) :
 seeded base flag column=base column := if_neg different
theorem seeded_value (base : Nat → F) (flag : Bool) :
 seeded base flag 7607=base 0+BooleanHints207.bitValue flag := if_pos rfl
variable [CharP F p]
theorem coefficient_cast : ((52435875175126190479447740508185965837690552500527637822603658699938581184512 : Int) : F)= -1 := by
 have equal : (52435875175126190479447740508185965837690552500527637822603658699938581184512 : Int)=(p : Int)-1 := by decide
 rw [equal,Int.cast_sub,Int.cast_natCast,Int.cast_one,CharP.cast_eq_zero F p,zero_sub]
theorem truth_iff (rho : Nat → F) : Truth rho recipe ↔ rho 7607=rho 0 ∨ rho 7607=rho 0+1 := by
 have expression : eval rho [(0,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7607,1)]=rho 7607-rho 0 := by
   simp only [eval,coefficient_cast,Int.cast_one,one_mul,add_zero]
   ring
 change Square (eval rho [(0,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7607,1)]) (eval rho [(0,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7607,1)]) ↔ _
 rw [expression]
 exact shifted_square _ _
theorem seeded_truth (base : Nat → F) (flag : Bool) : Truth (seeded base flag) recipe := by
 apply (truth_iff _).mpr
 rw [seeded_value,seeded_outside base flag 0 (by decide)]
 cases flag <;> simp [BooleanHints207.bitValue]
theorem candidate_truth (base : Nat → F) (flag : Bool) :
 Truth (CapturedFullRelation58.candidate (seeded base flag)) recipe := by
 apply (truth_iff _).mpr
 have original:=CapturedFullRelation58.candidate_inputs (seeded base flag) 7604 (by decide)
 have zero:=CapturedFullRelation58.candidate_outside (seeded base flag) 0 (by decide) (by decide)
 change CapturedFullRelation58.candidate (seeded base flag) 7607=seeded base flag 7607 at original
 rw [original,zero]
 exact (truth_iff _).mp (seeded_truth base flag)
theorem selected (base : Nat → F) (flag : Bool) :
 ∃ row,CapturedFullRelation58.rowAt 185429=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base flag)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base flag)) row.b) := by
 obtain ⟨row,hint,found,specified,check⟩:=CapturedFullAssertions54.block.exact_checked 7475 (by decide)
 have equal : hint=(true,recipe) := Option.some.inj (specified.symm.trans checked)
 have truth : Truth (CapturedFullRelation58.candidate (seeded base flag)) hint.2 := by
   rw [equal]
   exact candidate_truth base flag
 refine ⟨row,?_,(CompilerAssertionBlock51.checked_iff copy row hint check _
   (CapturedFullRelation58.candidate_links (seeded base flag)).2.2).mpr truth⟩
 rw [CapturedFullRelation58.assertion_position 7475 (by decide)]
 exact found
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 rho 7607=rho 0 ∨ rho 7607=rho 0+1 :=
 (truth_iff rho).mp (((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 7475 (by decide) _ checked)
theorem tag_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (zero : rho 0=1) : rho 7607=1 ∨ rho 7607=2 := by
 have tag:=sound rho satisfied
 simpa only [zero,one_add_one_eq_two] using tag
end ShielddSecurity.CapturedOriginalTag214
'''
names=['recipe','checked','shifted_square','coefficient_cast','truth_iff','seeded','seeded_outside','seeded_value','seeded_truth','candidate_truth','selected','sound','tag_sound']
inputs=[qp,p,W/'mac-boolean-hints207-source05/source-root/ShielddSecurity/BooleanHints207.lean',W/'mac-full-captured-relation58-source02/source-root/ShielddSecurity/CapturedFullRelation58.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-word-hints210-source03/generate.py').read_bytes())
(S/'selected-data01.json').write_text(json.dumps(dict(record=r,qualification=pin(qp),chunk=chunk['data'],scope='Exact original shifted-square predicate, copy outlining checked as DATA; no kernel/native credit.'),sort_keys=True,separators=(',',':'))+'\n')
inputs.append(S/'selected-data01.json')
(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedOriginalTag214':dict(body=body,names=names)},inputs={str(p):pin(p)for p in inputs},scope='SOURCE_ONLY_UNRUN13 planned reports. Captured p-1 coefficient normalized via CharP; original02 entire failed module ZERO. Actual shifted original square at185429; tag7607 is rho0 or rho0+1, not Boolean0/1. Explicit single-column seed, candidate selected row and full-relation soundness, tag1/2 under explicit rho0=1. No caller/native meaning, simultaneous seed/global legal witness/full Transfer claim.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(stage=str(S),planned_audits=len(names))))
