import ShielddSecurity.UserLifecycleBits344
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.QuaternarySelector944
def children {A : Type} (slot : Nat) (node s0 s1 s2 : A) : List A :=
  if slot=0 then [node,s0,s1,s2] else if slot=1 then [s0,node,s1,s2]
  else if slot=2 then [s0,s1,node,s2] else [s0,s1,s2,node]
theorem select {F : Type} [Field F] (lo hi : Bool) (node s0 s1 s2 : F) :
    let l := BooleanHints207.bitValue (F:=F) lo*(s0-node)
    let r := BooleanHints207.bitValue (F:=F) lo*(s2-node)
    let h := BooleanHints207.bitValue (F:=F) hi
    [node+l+h*(s0-(node+l)),s0-l+h*(s1-(s0-l)),s1+h*(node+r-s1),s2+h*((s2-r)-s2)]=
      children (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) node s0 s1 s2 := by
  cases lo <;> cases hi <;> simp [children,BooleanHints207.bitValue] <;> ring_nf

theorem bit_slot (position level : Nat) :
    (if decide (position/2^(2*level+1)%2=1) then
      (if decide (position/2^(2*level)%2=1) then 3 else 2)
    else (if decide (position/2^(2*level)%2=1) then 1 else 0))=position/4^level%4 := by
  have powers : 2^(2*level)=4^level := by rw [pow_mul];rfl
  rw [Nat.pow_succ,powers,←Nat.div_div_eq_div_mul]
  by_cases lo : position/4^level%2=1 <;> by_cases hi : position/4^level/2%2=1 <;>
    simp only [lo,hi,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] <;> omega

theorem encoded_slot (position level : Nat) (inside : level<24) :
    (if (encodeBits 48 position)[2*level+1]?.getD false then
      (if (encodeBits 48 position)[2*level]?.getD false then 3 else 2)
    else (if (encodeBits 48 position)[2*level]?.getD false then 1 else 0))=position/4^level%4 := by
  rw [UserLifecycleBits344.encoded_bit 48 position (2*level+1) (by omega),
    UserLifecycleBits344.encoded_bit 48 position (2*level) (by omega)]
  exact bit_slot position level

theorem map_children {A B : Type} (f : A → B) (slot : Nat) (node s0 s1 s2 : A) :
    (children slot node s0 s1 s2).map f=children slot (f node) (f s0) (f s1) (f s2) := by
  by_cases h0 : slot=0
  · simp only [children,if_pos h0,List.map_cons,List.map_nil]
  · by_cases h1 : slot=1
    · simp only [children,if_neg h0,if_pos h1,List.map_cons,List.map_nil]
    · by_cases h2 : slot=2
      · simp only [children,if_neg h0,if_neg h1,if_pos h2,List.map_cons,List.map_nil]
      · simp only [children,if_neg h0,if_neg h1,if_neg h2,List.map_cons,List.map_nil]
end ShielddSecurity.QuaternarySelector944

set_option pp.all true in
#check @ShielddSecurity.QuaternarySelector944.select
#print axioms ShielddSecurity.QuaternarySelector944.select

set_option pp.all true in
#check @ShielddSecurity.QuaternarySelector944.bit_slot
#print axioms ShielddSecurity.QuaternarySelector944.bit_slot

set_option pp.all true in
#check @ShielddSecurity.QuaternarySelector944.encoded_slot
#print axioms ShielddSecurity.QuaternarySelector944.encoded_slot

set_option pp.all true in
#check @ShielddSecurity.QuaternarySelector944.map_children
#print axioms ShielddSecurity.QuaternarySelector944.map_children
