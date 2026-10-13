import ShielddSecurity.QuotientComparison381
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.QuotientNumeric382
open Compiler CompilerArithmeticTransport41 ComparisonCertificate101 BinaryComparison100

def bitAt (n column : Nat) : Bool := (encodeBits 4 n)[column-1996]?.getD false

def leadingMaximum (n : Nat) : List (Bool × Bool) :=
  (List.range' 1996 0).map (fun column => (bitAt n column,true))

def pairs (n : Nat) : List (Bool × Bool) :=
  leadingMaximum n ++ ((bitAt n 1996,false)::QuotientComparison381.entries.map
    (fun entry => (bitAt n entry.bitColumn,entry.maximumBit)))

theorem columns_exact : List.range' 1996 0 ++
    (1996::QuotientComparison381.entries.map Entry.bitColumn)=List.range' 1996 4 := by decide +kernel

theorem tail_columns_exact : 1996::QuotientComparison381.entries.map Entry.bitColumn=List.range' 1996 4 := by decide +kernel

theorem left_exact (n : Nat) : (pairs n).map Prod.fst=encodeBits 4 n := by
  calc
    _ = (List.range' 1996 0 ++ (1996::QuotientComparison381.entries.map Entry.bitColumn)).map (bitAt n) := by
      simp only [pairs,leadingMaximum,List.map_append,List.map_cons,List.map_map,Function.comp_def]
    _ = (List.range' 1996 4).map (bitAt n) := by rw [columns_exact]
    _ = _ := by
      apply List.ext_getElem
      · simp only [List.length_map,List.length_range',encodeBits_length]
      · intro index a b
        simp only [List.getElem_map,List.getElem_range',Nat.one_mul,bitAt,Nat.add_sub_cancel_left]
        rw [List.getElem?_eq_getElem b]
        rfl

theorem right_exact (n : Nat) : (pairs n).map Prod.snd=encodeBits 4 8 := by
  simp only [pairs,leadingMaximum,List.map_append,List.map_cons,List.map_map,Function.comp_def,Prod.snd]
  decide +kernel

theorem numeric_bound (n : Nat) (bound : n≤8) :
    binary ((pairs n).map Prod.fst)≤binary ((pairs n).map Prod.snd) := by
  have last : 8<2^4 := by decide
  rw [left_exact,right_exact,encodeBits_value 4 n (lt_of_le_of_lt bound last),encodeBits_value 4 8 last]
  exact bound

variable {F : Type} [Field F]

theorem scan_append (flag : F) (left right : List (Bool × Bool)) :
    scan flag (left++right)=scan (scan flag left) right := by
  induction left generalizing flag with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem right_one_step (a : Bool) : step (1:F) (bit a) (bit true)=1 := by
  unfold step
  change (1-bit a)*1+1*((1-bit a)+1-((1-bit a)*1+(1-bit a)*1))=1
  ring

theorem scan_true_prefix (bits : List Bool) : scan (1:F) (bits.map (fun a => (a,true)))=1 := by
  induction bits with
  | nil => rfl
  | cons a tail ih =>
    change scan (step (1:F) (bit a) (bit true)) (tail.map (fun a => (a,true)))=1
    rw [right_one_step]
    exact ih

theorem prefix_scan (n : Nat) : scan (1:F) (leadingMaximum n)=1 := by
  simpa only [leadingMaximum,List.map_map,Function.comp_def] using
    (scan_true_prefix (F:=F) ((List.range' 1996 0).map (bitAt n)))

theorem head_false_step (a : Bool) : step (1:F) (bit a) (bit false)=1-bit a := by
  unfold step
  change (1-bit a)*0+1*((1-bit a)+0-((1-bit a)*0+(1-bit a)*0))=1-bit a
  ring

theorem whole_scan (n : Nat) : compare (F:=F) (pairs n)=
    scan (1-bit (bitAt n 1996)) (QuotientComparison381.entries.map
      (fun entry => (bitAt n entry.bitColumn,entry.maximumBit))) := by
  unfold BinaryComparison100.compare pairs
  rw [scan_append,prefix_scan]
  change scan (step (1:F) (bit (bitAt n 1996)) (bit false)) _ = _
  rw [head_false_step]

variable [CharP F p]

theorem semantic (rho : Nat → F) (n : Nat) (bound : n≤8) (one : rho copy=1)
    (arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<4,rho (1996+index)=bit (F:=F) (bitAt n (1996+index))) :
    1-rho 1999+rho 50204=1 := by
  have matched : ∀ entry∈QuotientComparison381.entries,
      rho entry.bitColumn=bit (F:=F) (bitAt n entry.bitColumn) := by
    intro entry member
    have col : entry.bitColumn∈1996::QuotientComparison381.entries.map Entry.bitColumn :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
    rw [tail_columns_exact] at col
    obtain ⟨index,indexBound,equal⟩ := List.mem_range'.mp col
    simp only [Nat.one_mul] at equal
    have shifted : entry.bitColumn=1996+(0+index) := by omega
    rw [shifted]
    exact values (0+index) (by omega)
  have h := QuotientComparison381.semantic rho one arithmetic
  rw [rawScan_boolean rho _ QuotientComparison381.entries (bitAt n) matched] at h
  have init : eval rho QuotientComparison381.initial=1-bit (F:=F) (bitAt n 1996) := by
    change eval rho [(1996,-1),(copy,1)]=_
    simp only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one]
    have v := values 0 (by decide)
    change rho 1996=bit (F:=F) (bitAt n 1996) at v
    rw [v]
    ring
  rw [init,←whole_scan n,compare_complete (pairs n) (numeric_bound n bound)] at h
  rw [QuotientComparison381.output_exact] at h
  have literal : rho 200692=1 := one
  simpa only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,literal,zero_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using h

end ShielddSecurity.QuotientNumeric382

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.bitAt
#print axioms ShielddSecurity.QuotientNumeric382.bitAt

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.leadingMaximum
#print axioms ShielddSecurity.QuotientNumeric382.leadingMaximum

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.pairs
#print axioms ShielddSecurity.QuotientNumeric382.pairs

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.columns_exact
#print axioms ShielddSecurity.QuotientNumeric382.columns_exact

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.tail_columns_exact
#print axioms ShielddSecurity.QuotientNumeric382.tail_columns_exact

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.left_exact
#print axioms ShielddSecurity.QuotientNumeric382.left_exact

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.right_exact
#print axioms ShielddSecurity.QuotientNumeric382.right_exact

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.numeric_bound
#print axioms ShielddSecurity.QuotientNumeric382.numeric_bound

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.scan_append
#print axioms ShielddSecurity.QuotientNumeric382.scan_append

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.right_one_step
#print axioms ShielddSecurity.QuotientNumeric382.right_one_step

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.scan_true_prefix
#print axioms ShielddSecurity.QuotientNumeric382.scan_true_prefix

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.prefix_scan
#print axioms ShielddSecurity.QuotientNumeric382.prefix_scan

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.head_false_step
#print axioms ShielddSecurity.QuotientNumeric382.head_false_step

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.whole_scan
#print axioms ShielddSecurity.QuotientNumeric382.whole_scan

set_option pp.all true in
#check @ShielddSecurity.QuotientNumeric382.semantic
#print axioms ShielddSecurity.QuotientNumeric382.semantic
