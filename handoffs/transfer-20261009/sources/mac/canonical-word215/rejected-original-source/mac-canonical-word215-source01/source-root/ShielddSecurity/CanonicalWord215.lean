import ShielddSecurity.ComparisonCertificate101
import ShielddSecurity.WordHints210
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalWord215
open Compiler CompilerArithmeticTransport41 ComparisonCertificate101
variable {F : Type} [Field F]
def decoded (rho : Nat → F) (column : Nat) : Bool := by
 classical
 exact decide (rho column=1)
theorem decoded_value (rho : Nat → F) (column : Nat)
 (boolean : Square (rho column) (rho column)) :
 BinaryComparison100.bit (decoded rho column)=rho column := by
 classical
 rcases boolean_sound (rho column) boolean with zero | one
 · simp only [decoded,zero,zero_ne_one,decide_false,BinaryComparison100.bit,Bool.false_eq_true,if_false]
 · simp only [decoded,one,decide_true,BinaryComparison100.bit,if_true]
def columns (first : Nat) (entries : List Entry) : List Nat :=
 first::entries.map Entry.bitColumn
def pairs (rho : Nat → F) (first : Nat) (entries : List Entry) : List (Bool × Bool) :=
 (decoded rho first,false)::entries.map (fun entry => (decoded rho entry.bitColumn,entry.maximumBit))
theorem left_bits (rho : Nat → F) (first : Nat) (entries : List Entry) :
 (pairs rho first entries).map Prod.fst=(columns first entries).map (decoded rho) := by
 simp only [pairs,columns,List.map_cons,List.map_map,Prod.fst]
 rfl
theorem binary_meaning (rho : Nat → F) (first value : Nat) (entries : List Entry)
 (booleans : ∀ column∈columns first entries,Square (rho column) (rho column))
 (reconstruction : fieldBinary ((columns first entries).map rho)=rho value) :
 (binary ((pairs rho first entries).map Prod.fst):F)=rho value := by
 have mapping : ((columns first entries).map (decoded rho)).map
   (fun flag => if flag then (1:F) else 0)=(columns first entries).map rho := by
   rw [List.map_map]
   apply List.map_congr_left
   intro column member
   exact decoded_value rho column (booleans column member)
 rw [left_bits,←binary_cast,mapping]
 exact reconstruction
variable [CharP F p]
theorem chain_compare (rho : Nat → F) (first : Nat) (initial : Linear) (entries : List Entry)
 (one : rho copy=1)
 (initial_checked : canonical p initial=canonical p [(copy,1),(first,-1)])
 (checked : chainCheck initial entries=true)
 (satisfied : Satisfies rho (entries.flatMap Entry.rows))
 (booleans : ∀ column∈columns first entries,Square (rho column) (rho column)) :
 eval rho (output initial entries)=BinaryComparison100.compare (pairs rho first entries) := by
 have leading := canonical_equal rho initial [(copy,1),(first,-1)] initial_checked
 have firstBoolean : Square (rho first) (rho first) := booleans first (List.mem_cons_self)
 have firstValue := decoded_value rho first firstBoolean
 have initialValue : eval rho initial=
   BinaryComparison100.step 1 (BinaryComparison100.bit (decoded rho first)) (BinaryComparison100.bit false) := by
   rw [leading,firstValue]
   simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,one,
     BinaryComparison100.step,BinaryComparison100.bit,Bool.false_eq_true,if_false,
     mul_zero,add_zero,sub_zero,mul_one]
   ring
 have values : ∀ entry∈entries,rho entry.bitColumn=BinaryComparison100.bit (decoded rho entry.bitColumn) := by
   intro entry member
   exact (decoded_value rho entry.bitColumn (booleans entry.bitColumn
     (List.mem_cons_of_mem first (List.mem_map.mpr ⟨entry,member,rfl⟩)))).symm
 rw [chain_sound rho initial entries one checked satisfied,initialValue,
   rawScan_boolean rho _ entries (decoded rho) values]
 rfl
theorem comparison_bound (rho : Nat → F) (first : Nat) (initial : Linear) (entries : List Entry)
 (one : rho copy=1)
 (initial_checked : canonical p initial=canonical p [(copy,1),(first,-1)])
 (checked : chainCheck initial entries=true)
 (satisfied : Satisfies rho (entries.flatMap Entry.rows))
 (booleans : ∀ column∈columns first entries,Square (rho column) (rho column))
 (accepted : eval rho (output initial entries)=1) :
 binary ((pairs rho first entries).map Prod.fst)≤binary ((pairs rho first entries).map Prod.snd) := by
 have semantic := chain_compare rho first initial entries one initial_checked checked satisfied booleans
 have result : BinaryComparison100.compare (pairs rho first entries)=1 := semantic.symm.trans accepted
 rw [BinaryComparison100.compare_exact] at result
 by_contra refused
 rw [if_neg refused] at result
 exact zero_ne_one result
theorem canonical_recovery (rho : Nat → F) (first value : Nat) (initial : Linear) (entries : List Entry)
 (one : rho copy=1)
 (initial_checked : canonical p initial=canonical p [(copy,1),(first,-1)])
 (checked : chainCheck initial entries=true)
 (satisfied : Satisfies rho (entries.flatMap Entry.rows))
 (booleans : ∀ column∈columns first entries,Square (rho column) (rho column))
 (accepted : eval rho (output initial entries)=1)
 (maximum : binary ((pairs rho first entries).map Prod.snd)=p-1)
 (reconstruction : fieldBinary ((columns first entries).map rho)=rho value) :
 ∃ n : Nat,n<p ∧ (n:F)=rho value := by
 have bound:=comparison_bound rho first initial entries one initial_checked checked satisfied booleans accepted
 rw [maximum] at bound
 refine ⟨binary ((pairs rho first entries).map Prod.fst),?_,
   binary_meaning rho first value entries booleans reconstruction⟩
 have positive : 0<p := by decide
 omega
end ShielddSecurity.CanonicalWord215

set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.decoded
#print axioms ShielddSecurity.CanonicalWord215.decoded
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.decoded_value
#print axioms ShielddSecurity.CanonicalWord215.decoded_value
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.columns
#print axioms ShielddSecurity.CanonicalWord215.columns
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.pairs
#print axioms ShielddSecurity.CanonicalWord215.pairs
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.left_bits
#print axioms ShielddSecurity.CanonicalWord215.left_bits
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.binary_meaning
#print axioms ShielddSecurity.CanonicalWord215.binary_meaning
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.chain_compare
#print axioms ShielddSecurity.CanonicalWord215.chain_compare
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.comparison_bound
#print axioms ShielddSecurity.CanonicalWord215.comparison_bound
set_option pp.all true in
#check @ShielddSecurity.CanonicalWord215.canonical_recovery
#print axioms ShielddSecurity.CanonicalWord215.canonical_recovery
