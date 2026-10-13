from pathlib import Path
import argparse,json
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();dst=out/'source-root/ShielddSecurity';dst.mkdir(parents=True)
for family in json.loads((root/'families.json').read_text()):
    name='Captured'+family['name']+'Lifecycle'+('346' if family['name']=='Sender' else '347')
    ar=family['arithmetic_start'];oc=family['output_start'];bc=family['bit_start'];ac=family['assertion_start'];count=family['count']
    t=f"""import ShielddSecurity.UserLifecycleBits344
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51

def bitIndex (index : Nat) : Nat := if index<3 then index else index+64
def output (index : Nat) : Nat := {oc}+2*index
def left : Linear := [(10,1)]
def right (index : Nat) : Linear :=
  [( {bc}+bitIndex index,1)] ++ (if index=0 then [(0,-1)] else [])

def arithmeticRows (index : Nat) : List Row :=
  [⟨[(10,1),({bc}+bitIndex index,(p:Int)-1)] ++ (if index=0 then [(copy,1)] else []),[(output index+1,1)]⟩,
   ⟨[(10,1),({bc}+bitIndex index,1)] ++ (if index=0 then [(copy,(p:Int)-1)] else []),[(output index,4),(output index+1,1)]⟩]

noncomputable def rowCheck : Bool := (List.range {count}).all (fun index => decide
  (CapturedFullArithmetic52.rowAt ({ar}+2*index)= (arithmeticRows index)[0]? ∧
   CapturedFullArithmetic52.rowAt ({ar}+2*index+1)= (arithmeticRows index)[1]?))
theorem row_checked : rowCheck=true := by decide +kernel

theorem arithmetic_position (index : Nat) (bound : index<{count}) :
    CapturedFullArithmetic52.rowAt ({ar}+2*index)= (arithmeticRows index)[0]? ∧
    CapturedFullArithmetic52.rowAt ({ar}+2*index+1)= (arithmeticRows index)[1]? :=
  of_decide_eq_true (List.all_eq_true.mp row_checked index (List.mem_range.mpr bound))

noncomputable def normalizedRows (index : Nat) : List Row :=
  (arithmeticRows index).map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)
noncomputable def pairCheck (index : Nat) : Bool :=
  Compiler.checkRow p (normalizedRows index) ⟨subtract left (right index),[(output index+1,1)]⟩ &&
  Compiler.checkRow p (normalizedRows index) ⟨left++right index,[(output index+1,1)]++scaleLinear 4 [(output index,1)]⟩
theorem production_checked : (List.range {count}).all pairCheck=true := by decide +kernel

variable {{F : Type}} [Field F] [CharP F p]
theorem products (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (linked : rho copy=rho 0) (index : Nat) (bound : index<{count}) :
    rho (output index)=rho 10*(rho ({bc}+bitIndex index)-(if index=0 then rho 0 else 0)) := by
  have positions := arithmetic_position index bound
  have sat : Satisfies rho (arithmeticRows index) := by
    intro row member
    simp only [arithmeticRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact arithmetic ({ar}+2*index) (by omega) _ positions.1
    · exact arithmetic ({ar}+2*index+1) (by omega) _ positions.2
  have normalized : Satisfies rho (normalizedRows index) := by
    intro row member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    change Square (eval rho (unoutline copy original.a)) (eval rho (unoutline copy original.b))
    rw [eval_unoutline rho copy original.a linked,eval_unoutline rho copy original.b linked]
    exact sat original present
  have checked := Bool.and_eq_true_iff.mp (List.all_eq_true.mp production_checked index (List.mem_range.mpr bound))
  have h := checked_product_sound rho (normalizedRows index) left (right index) [(output index,1)] [(output index+1,1)]
    four_ne_zero normalized checked.1 checked.2
  by_cases zero : index=0
  · simpa only [left,right,if_pos zero,List.append_assoc,List.cons_append,List.nil_append,
      eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,sub_eq_add_neg] using h
  · simpa only [left,right,if_neg zero,List.append_nil,
      eval,Int.cast_one,one_mul,add_zero,sub_zero] using h

def actualRow (index : Nat) : Row := ⟨[(output index,(p:Int)-1)],[]⟩
noncomputable def assertionCheck : Bool := (List.range {count}).all (fun index =>
  decide (CapturedFullRelation58.rowAt (177954+{ac}+index)=some (actualRow index)))
theorem assertion_checked : assertionCheck=true := by decide +kernel

theorem actual_position (index : Nat) (bound : index<{count}) :
    CapturedFullRelation58.rowAt (177954+{ac}+index)=some (actualRow index) :=
  of_decide_eq_true (List.all_eq_true.mp assertion_checked index (List.mem_range.mpr bound))

theorem complete (rho : Nat → F) (values : ∀ index<{count},rho (output index)=0) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (177954+{ac}+index)) {count} := by
  intro index bound row found
  have same : actualRow index=row := Option.some.inj ((actual_position index bound).symm.trans found)
  subst row
  change Square (eval rho [(output index,(p:Int)-1)]) (eval rho [])
  simp only [eval,values index bound,mul_zero,add_zero,Square]
end ShielddSecurity.{name}

"""
    for declaration in ['bitIndex','output','left','right','arithmeticRows','rowCheck','row_checked','arithmetic_position','normalizedRows','pairCheck','production_checked','products','actualRow','assertionCheck','assertion_checked','actual_position','complete']:
        t+=f'set_option pp.all true in\n#check @ShielddSecurity.{name}.{declaration}\n#print axioms ShielddSecurity.{name}.{declaration}\n\n'
    (dst/(name+'.lean')).write_text(t.rstrip()+'\n')
print(json.dumps({'status':'generated','modules':2}))
