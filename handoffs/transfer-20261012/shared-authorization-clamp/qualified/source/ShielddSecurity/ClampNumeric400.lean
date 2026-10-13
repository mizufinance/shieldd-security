import ShielddSecurity.AuthorizationClamp398
import ShielddSecurity.ClampCapture399
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ClampNumeric400
open Compiler CompilerArithmeticTransport41 ComparisonCertificate101 BinaryComparison100
def bitAt (n column : Nat) : Bool := (encodeBits 252 n)[column-2000]?.getD false
def pairs (n : Nat) : List (Bool × Bool) :=
    (bitAt n 2000,false)::ClampCapture399.entries.map (fun entry => (bitAt n entry.bitColumn,entry.maximumBit))
theorem columns_exact : 2000::ClampCapture399.entries.map Entry.bitColumn=List.range' 2000 252 := by decide +kernel
theorem maximum_exact : false::ClampCapture399.entries.map Entry.maximumBit=encodeBits 252 AuthorizationClamp398.maximum := by decide +kernel
theorem left_exact (n : Nat) : (pairs n).map Prod.fst=encodeBits 252 n := by
  calc
    (pairs n).map Prod.fst=(2000::ClampCapture399.entries.map Entry.bitColumn).map (bitAt n) := by
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
theorem right_exact (n : Nat) : (pairs n).map Prod.snd=encodeBits 252 AuthorizationClamp398.maximum := by
  simpa only [pairs,List.map_cons,List.map_map,Function.comp_def,Prod.snd] using maximum_exact
theorem numeric_bound (n : Nat) (bound : n≤AuthorizationClamp398.maximum) :
    binary ((pairs n).map Prod.fst)≤binary ((pairs n).map Prod.snd) := by
  have maximum : AuthorizationClamp398.maximum<2^252 := by decide +kernel
  rw [left_exact,right_exact,encodeBits_value 252 n (lt_of_le_of_lt bound maximum),encodeBits_value 252 AuthorizationClamp398.maximum maximum]
  exact bound
variable {F : Type} [Field F] [CharP F p]
theorem semantic (rho : Nat → F) (n : Nat) (one : rho copy=1)
    (arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<252,rho (2000+index)=bit (F:=F) (bitAt n (2000+index))) :
    rho 51208=BinaryComparison100.compare (F:=F) (pairs n) := by
  have matched : ∀ entry∈ClampCapture399.entries,
      rho entry.bitColumn=bit (F:=F) (bitAt n entry.bitColumn) := by
    intro entry member
    have col : entry.bitColumn∈2000::ClampCapture399.entries.map Entry.bitColumn :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
    rw [columns_exact] at col
    obtain ⟨index,indexBound,equal⟩:=List.mem_range'.mp col
    simp only [one_mul] at equal
    rw [equal]
    exact values index indexBound
  have h:=ClampCapture399.semantic rho one arithmetic
  have raw:=rawScan_boolean rho (eval rho ClampCapture399.initial)
    ClampCapture399.entries (bitAt n) matched
  rw [raw,ClampCapture399.output_exact] at h
  change eval rho [(51208,1)]=_ at h
  have init : eval rho ClampCapture399.initial=1-bit (F:=F) (bitAt n 2000) := by
    change eval rho [(2000,-1),(copy,1)]=_
    simp only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one]
    rw [values 0 (by decide)]
    ring
  have head : BinaryComparison100.step (1:F) (bit (bitAt n 2000)) (bit false)=1-bit (bitAt n 2000) := by
    change (1-bit (F:=F) (bitAt n 2000))*0+1*((1-bit (F:=F) (bitAt n 2000))+0-((1-bit (F:=F) (bitAt n 2000))*0+(1-bit (F:=F) (bitAt n 2000))*0))=_
    ring
  have all : eval rho [(51208,1)]=compare (F:=F) (pairs n) := by
    rw [h,init]
    change _=scan (step (1:F) (bit (bitAt n 2000)) (bit false)) _
    rw [head]
  simpa only [eval,Int.cast_one,one_mul,add_zero] using all
end ShielddSecurity.ClampNumeric400

set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.bitAt
#print axioms ShielddSecurity.ClampNumeric400.bitAt
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.pairs
#print axioms ShielddSecurity.ClampNumeric400.pairs
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.columns_exact
#print axioms ShielddSecurity.ClampNumeric400.columns_exact
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.maximum_exact
#print axioms ShielddSecurity.ClampNumeric400.maximum_exact
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.left_exact
#print axioms ShielddSecurity.ClampNumeric400.left_exact
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.right_exact
#print axioms ShielddSecurity.ClampNumeric400.right_exact
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.numeric_bound
#print axioms ShielddSecurity.ClampNumeric400.numeric_bound
set_option pp.all true in
#check @ShielddSecurity.ClampNumeric400.semantic
#print axioms ShielddSecurity.ClampNumeric400.semantic
