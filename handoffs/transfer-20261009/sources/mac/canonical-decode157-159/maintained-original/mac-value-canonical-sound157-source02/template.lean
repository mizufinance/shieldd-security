import ShielddSecurity.CapturedValueCanonical107
import ShielddSecurity.BooleanDecode150
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedValueCanonicalSound157
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101 BinaryComparison100 CapturedValueComparison106
variable {F : Type} [Field F] [CharP F p]
theorem scan_exact (rho : Nat → F) (n : Nat) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (values : ∀ index<255,rho (216+index)=bit (F:=F) (bitAt n (216+index))) :
    1-rho 470+rho 32752=compare (F:=F) (pairs n) := by
  have matched : ∀ entry∈CapturedValueComparison105.entries,
      rho entry.bitColumn=bit (F:=F) (bitAt n entry.bitColumn) := by
    intro entry member
    have col : entry.bitColumn∈216::CapturedValueComparison105.entries.map Entry.bitColumn :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,member,rfl⟩)
    rw [columns_exact] at col
    obtain ⟨index,indexBound,equal⟩:=List.mem_range'.mp col
    simp only [one_mul] at equal
    rw [equal]
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
  simpa only [eval,Int.cast_neg,Int.cast_one,neg_mul,one_mul,add_zero,one,zero_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using all
theorem canonical_truth (rho : Nat → F)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1) :
    1-rho 470+rho 32752=1 := by
  have linked:=(CapturedFullRelation58.verifier_links rho satisfied).2.2
  have localRows : SatisfiesAt rho CapturedValueCanonical107.block.actual 2 := by
    intro index bound row found
    apply satisfied (178375+index) (by omega) row
    rw [CapturedValueCanonical107.full_position index bound]
    exact found
  have truth:=(CompilerAssertionBlock51.satisfies_iff copy 2 CapturedValueCanonical107.block rho linked).mp localRows
  have value:=truth 1 (by decide) (true,CapturedValueCanonical107.expected 1)
    (CapturedValueCanonical107.hint_exact 1 (by decide))
  change eval rho [(0,1)]=eval rho CapturedValueCanonical107.valueLC at value
  have normalization : canonical p CapturedValueCanonical107.valueLC=canonical p [(0,1),(470,-1),(32752,1)] := by decide +kernel
  have normalized:=canonical_equal rho CapturedValueCanonical107.valueLC [(0,1),(470,-1),(32752,1)] normalization
  rw [normalized] at value
  simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero,one,sub_eq_add_neg,add_assoc] using value.symm
theorem canonical_bound (rho : Nat → F) (n : Nat) (bound : n<2^255)
    (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) (one : rho 0=1)
    (values : ∀ index<255,rho (216+index)=bit (F:=F) (bitAt n (216+index))) : n<p := by
  have copyOne:=((CapturedFullRelation58.verifier_links rho satisfied).2.2).trans one
  have scan:=scan_exact rho n copyOne ((CapturedFullRelation58.satisfies_split rho).mp satisfied).1 values
  rw [canonical_truth rho satisfied one,compare_exact,left_exact,right_exact,
    encodeBits_value 255 n bound,encodeBits_value 255 (p-1) (by decide)] at scan
  have before : n≤p-1 := by
    by_contra notBefore
    rw [if_neg notBefore] at scan
    exact one_ne_zero scan
  have positive : 0<p := by decide
  omega
end ShielddSecurity.CapturedValueCanonicalSound157
