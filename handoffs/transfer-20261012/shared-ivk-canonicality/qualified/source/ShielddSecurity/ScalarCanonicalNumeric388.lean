import ShielddSecurity.TransferCore
import ShielddSecurity.ScalarCanonicalCapture387
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ScalarCanonicalNumeric388
open Compiler CompilerArithmeticTransport41 ComparisonCertificate101 BinaryComparison100
def bitAt (n column : Nat) : Bool := (encodeBits 252 n)[column-2000]?.getD false
def pairs (n : Nat) : List (Bool × Bool) :=
    (bitAt n 2000,false)::ScalarCanonicalCapture387.entries.map (fun entry => (bitAt n entry.bitColumn,entry.maximumBit))
theorem columns_exact : 2000::ScalarCanonicalCapture387.entries.map Entry.bitColumn=List.range' 2000 252 := by decide +kernel
theorem maximum_exact : false::ScalarCanonicalCapture387.entries.map Entry.maximumBit=encodeBits 252 (TransferCore.scalarOrder-1) := by decide +kernel
theorem left_exact (n : Nat) : (pairs n).map Prod.fst=encodeBits 252 n := by
  calc
    (pairs n).map Prod.fst=(2000::ScalarCanonicalCapture387.entries.map Entry.bitColumn).map (bitAt n) := by
      simp only [pairs,List.map_cons,List.map_map,Function.comp_def]
    _ = (List.range' 2000 252).map (bitAt n) := by rw [columns_exact]
    _ = encodeBits 252 n := by
      apply List.ext_getElem
      · simp only [List.length_map,List.length_range',encodeBits_length]
      · intro index a b
        have bound : index<252 := by simpa only [encodeBits_length] using b
        simp only [List.getElem_map,List.getElem_range',Nat.one_mul,bitAt,Nat.add_sub_cancel_left]
        rw [List.getElem?_eq_getElem b]
        rfl
theorem right_exact (n : Nat) : (pairs n).map Prod.snd=encodeBits 252 (TransferCore.scalarOrder-1) := by
  simpa only [pairs,List.map_cons,List.map_map,Function.comp_def,Prod.snd] using maximum_exact
theorem numeric_bound (n : Nat) (bound : n<TransferCore.scalarOrder) :
    binary ((pairs n).map Prod.fst)≤binary ((pairs n).map Prod.snd) := by
  rw [left_exact,right_exact,encodeBits_value 252 n (Nat.lt_trans bound (by decide)),
    encodeBits_value 252 (TransferCore.scalarOrder-1) (by decide)]
  omega
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (n : Nat) (bound : n<TransferCore.scalarOrder) (one : rho copy=1)
    (arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<252,rho (2000+index)=bit (F:=F) (bitAt n (2000+index))) :
    1-rho 2251+rho 50706=1 := by
  have matched : ∀ entry∈ScalarCanonicalCapture387.entries,
      rho entry.bitColumn=bit (F:=F) (bitAt n entry.bitColumn) := by
    intro entry member
    have col : entry.bitColumn∈2000::ScalarCanonicalCapture387.entries.map Entry.bitColumn :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
    rw [columns_exact] at col
    obtain ⟨index,indexBound,equal⟩:=List.mem_range'.mp col
    simp only [one_mul] at equal
    rw [equal]
    exact values index indexBound
  have h:=ScalarCanonicalCapture387.semantic rho one arithmetic
  have raw:=rawScan_boolean rho (eval rho ScalarCanonicalCapture387.initial)
    ScalarCanonicalCapture387.entries (bitAt n) matched
  rw [raw,ScalarCanonicalCapture387.output_exact] at h
  change eval rho [(2251,-1),(50706,1),(copy,1)]=_ at h
  have init : eval rho ScalarCanonicalCapture387.initial=1-bit (F:=F) (bitAt n 2000) := by
    change eval rho [(2000,-1),(copy,1)]=_
    simp only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one]
    rw [values 0 (by decide)]
    ring
  have head : BinaryComparison100.step (1:F) (bit (bitAt n 2000)) (bit false)=1-bit (bitAt n 2000) := by
    change (1-bit (F:=F) (bitAt n 2000))*0+1*((1-bit (F:=F) (bitAt n 2000))+0-((1-bit (F:=F) (bitAt n 2000))*0+(1-bit (F:=F) (bitAt n 2000))*0))=_
    ring
  have all : eval rho [(2251,-1),(50706,1),(copy,1)]=compare (F:=F) (pairs n) := by
    rw [h,init]
    change _=scan (step (1:F) (bit (bitAt n 2000)) (bit false)) _
    rw [head]
  rw [compare_complete (pairs n) (numeric_bound n bound)] at all
  simpa only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one,zero_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using all
end ShielddSecurity.ScalarCanonicalNumeric388

set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.bitAt
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.bitAt
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.pairs
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.pairs
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.columns_exact
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.columns_exact
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.maximum_exact
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.maximum_exact
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.left_exact
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.left_exact
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.right_exact
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.right_exact
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.numeric_bound
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.numeric_bound
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalNumeric388.semantic
#print axioms ShielddSecurity.ScalarCanonicalNumeric388.semantic
