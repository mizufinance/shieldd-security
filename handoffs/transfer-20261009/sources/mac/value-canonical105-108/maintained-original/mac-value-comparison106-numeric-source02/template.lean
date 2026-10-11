import ShielddSecurity.CapturedValueComparison105
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueComparison106
open Compiler CompilerArithmeticTransport41 ComparisonCertificate101 BinaryComparison100
def bitAt (n column : Nat) : Bool := (encodeBits 255 n)[column-216]?.getD false
def pairs (n : Nat) : List (Bool × Bool) :=
    (bitAt n 216,false)::CapturedValueComparison105.entries.map (fun entry => (bitAt n entry.bitColumn,entry.maximumBit))
theorem columns_exact : 216::CapturedValueComparison105.entries.map Entry.bitColumn=List.range' 216 255 := by decide +kernel
theorem maximum_exact : false::CapturedValueComparison105.entries.map Entry.maximumBit=encodeBits 255 (p-1) := by decide +kernel
theorem left_exact (n : Nat) : (pairs n).map Prod.fst=encodeBits 255 n := by
  calc
    (pairs n).map Prod.fst=(216::CapturedValueComparison105.entries.map Entry.bitColumn).map (bitAt n) := by
      simp only [pairs,List.map_cons,List.map_map,Function.comp_def,Prod.fst]
    _ = (List.range' 216 255).map (bitAt n) := by rw [columns_exact]
    _ = encodeBits 255 n := by
      apply List.ext_getElem
      · simp only [List.length_map,List.length_range',encodeBits_length]
      · intro index a b
        have bound : index<255 := by simpa only [encodeBits_length] using b
        simp only [List.getElem_map,List.getElem_range',Nat.mul_one,bitAt,Nat.add_sub_cancel_left,
          List.getElem?_eq_getElem (by simpa only [encodeBits_length] using bound),Option.getD_some]
theorem right_exact (n : Nat) : (pairs n).map Prod.snd=encodeBits 255 (p-1) := by
  simpa only [pairs,List.map_cons,List.map_map,Function.comp_def,Prod.snd] using maximum_exact
theorem numeric_bound (n : Nat) (bound : n<p) :
    binary ((pairs n).map Prod.fst)≤binary ((pairs n).map Prod.snd) := by
  rw [left_exact,right_exact,encodeBits_value 255 n (Nat.lt_trans bound (by decide)),
    encodeBits_value 255 (p-1) (by decide)]
  omega
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (n : Nat) (bound : n<p) (one : rho copy=1)
    (arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<255,rho (216+index)=bit (F:=F) (bitAt n (216+index))) :
    1-rho 470+rho 32752=1 := by
  have matched : ∀ entry∈CapturedValueComparison105.entries,
      rho entry.bitColumn=bit (F:=F) (bitAt n entry.bitColumn) := by
    intro entry member
    have col : entry.bitColumn∈216::CapturedValueComparison105.entries.map Entry.bitColumn :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
    rw [columns_exact] at col
    obtain ⟨index,indexBound,equal⟩:=List.mem_range'.mp col
    simp only [one_mul] at equal
    rw [←equal]
    exact values index indexBound
  have h:=CapturedValueComparison105.semantic rho one arithmetic
  have raw:=rawScan_boolean rho (eval rho CapturedValueComparison105.initial)
    CapturedValueComparison105.entries (bitAt n) matched
  rw [raw] at h
  have init : eval rho CapturedValueComparison105.initial=1-bit (F:=F) (bitAt n 216) := by
    change eval rho [(216,-1),(copy,1)]=_
    simp only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one]
    rw [values 0 (by decide)]
    ring
  have head : BinaryComparison100.step (1:F) (bit (bitAt n 216)) (bit false)=1-bit (bitAt n 216) := by
    change (1-bit (F:=F) (bitAt n 216))*0+1*((1-bit (F:=F) (bitAt n 216))+0-((1-bit (F:=F) (bitAt n 216))*0+(1-bit (F:=F) (bitAt n 216))*0))=_
    ring
  have all : eval rho [(470,-1),(32752,1),(copy,1)]=compare (F:=F) (pairs n) := by
    rw [h,init]
    change _=scan (step (1:F) (bit (bitAt n 216)) (bit false)) _
    rw [head]
  rw [compare_complete (pairs n) (numeric_bound n bound)] at all
  simpa only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using all
end ShielddSecurity.CapturedValueComparison106

set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.bitAt
#print axioms ShielddSecurity.CapturedValueComparison106.bitAt
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.pairs
#print axioms ShielddSecurity.CapturedValueComparison106.pairs
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.columns_exact
#print axioms ShielddSecurity.CapturedValueComparison106.columns_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.maximum_exact
#print axioms ShielddSecurity.CapturedValueComparison106.maximum_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.left_exact
#print axioms ShielddSecurity.CapturedValueComparison106.left_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.right_exact
#print axioms ShielddSecurity.CapturedValueComparison106.right_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.numeric_bound
#print axioms ShielddSecurity.CapturedValueComparison106.numeric_bound
set_option pp.all true in
#check @ShielddSecurity.CapturedValueComparison106.semantic
#print axioms ShielddSecurity.CapturedValueComparison106.semantic
