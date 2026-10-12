import ShielddSecurity.SharedWordFlags220
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.WordFlagCompatibility250
open WordHints210 SharedWordFlags220
def bitAt (n i : Nat) : Bool := decide (n/2^i%2=1)
theorem pair_offset (start width n : Nat) (pair : Nat × Bool)
 (member : pair∈(List.range' start width).zip (encodeBits width n)) :
 ∃ i<width,pair=(start+i,bitAt n i) := by
 induction width generalizing start n with
 | zero => simp only [List.range'_zero,encodeBits,List.zip_nil_left,List.not_mem_nil] at member
 | succ width ih =>
   simp only [List.range'_succ,encodeBits,List.zip_cons_cons,List.mem_cons] at member
   rcases member with same|tail
   · subst pair
     refine ⟨0,by omega,?_⟩
     simp only [Nat.add_zero,bitAt,Nat.pow_zero,Nat.div_one]
   · obtain ⟨i,bound,equal⟩:=ih (start+1) (n/2) tail
     refine ⟨i+1,by omega,equal.trans ?_⟩
     have bit : bitAt (n/2) i=bitAt n (i+1) := by
       simp only [bitAt,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm]
     rw [bit]
     congr 1
     omega
def shape (a b : Slot) (exceptions : List (Nat × Nat)) : Bool := decide
 (a.start+a.width≤b.start ∨ b.start+b.width≤a.start ∨
  (a.start=b.start ∧ a.value=b.value) ∨
  (a.width=1 ∧ a.start=b.start ∧ (a.value,b.value)∈exceptions) ∨
  (b.width=1 ∧ a.start=b.start ∧ (b.value,a.value)∈exceptions))
def check (slots : List Slot) (exceptions : List (Nat × Nat)) : Bool :=
 slots.all (fun a => slots.all (fun b => shape a b exceptions))
def LowAgree (exceptions : List (Nat × Nat)) (numbers : Nat → Nat) : Prop :=
 ∀ pair∈exceptions,bitAt (numbers pair.1) 0=bitAt (numbers pair.2) 0
theorem offsets_agree (slots : List Slot) (exceptions : List (Nat × Nat))
 (numbers : Nat → Nat) (checked : check slots exceptions=true) (low : LowAgree exceptions numbers)
 (a : Slot) (knownA : a∈slots) (b : Slot) (knownB : b∈slots)
 (i j : Nat) (hi : i<a.width) (hj : j<b.width) (same : a.start+i=b.start+j) :
 bitAt (numbers a.value) i=bitAt (numbers b.value) j := by
 have cases:shape a b exceptions=true :=
   List.all_eq_true.mp (List.all_eq_true.mp checked a knownA) b knownB
 simp only [shape,decide_eq_true_eq] at cases
 rcases cases with disjoint|disjoint|⟨start,value⟩|⟨width,start,present⟩|⟨width,start,present⟩
 · omega
 · omega
 · have index:i=j := by omega
   rw [value,index]
 · have zeroI:i=0 := by omega
   have zeroJ:j=0 := by omega
   subst i;subst j
   exact low _ present
 · have zeroI:i=0 := by omega
   have zeroJ:j=0 := by omega
   subst i;subst j
   exact (low _ present).symm
theorem coherent (slots : List Slot) (exceptions : List (Nat × Nat))
 (numbers : Nat → Nat) (checked : check slots exceptions=true) (low : LowAgree exceptions numbers) :
 Coherent (assignments slots numbers) := by
 intro pair pairMember other otherMember same
 obtain ⟨a,knownA,pairMember⟩:=List.mem_flatMap.mp pairMember
 obtain ⟨b,knownB,otherMember⟩:=List.mem_flatMap.mp otherMember
 obtain ⟨i,hi,equal⟩:=pair_offset a.start a.width (numbers a.value) pair pairMember
 obtain ⟨j,hj,otherEqual⟩:=pair_offset b.start b.width (numbers b.value) other otherMember
 subst pair;subst other
 exact offsets_agree slots exceptions numbers checked low a knownA b knownB i j hi hj same
end ShielddSecurity.WordFlagCompatibility250

set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.bitAt
#print axioms ShielddSecurity.WordFlagCompatibility250.bitAt
set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.pair_offset
#print axioms ShielddSecurity.WordFlagCompatibility250.pair_offset
set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.shape
#print axioms ShielddSecurity.WordFlagCompatibility250.shape
set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.check
#print axioms ShielddSecurity.WordFlagCompatibility250.check
set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.LowAgree
#print axioms ShielddSecurity.WordFlagCompatibility250.LowAgree
set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.offsets_agree
#print axioms ShielddSecurity.WordFlagCompatibility250.offsets_agree
set_option pp.all true in
#check @ShielddSecurity.WordFlagCompatibility250.coherent
#print axioms ShielddSecurity.WordFlagCompatibility250.coherent
