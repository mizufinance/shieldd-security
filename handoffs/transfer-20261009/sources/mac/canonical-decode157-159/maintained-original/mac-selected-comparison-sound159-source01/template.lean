import ShielddSecurity.CapturedValueComparison106
import ShielddSecurity.CompilerColumnRenaming05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SelectedComparisonSound159
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101 BinaryComparison100 CapturedValueComparison106
variable {F : Type} [Field F] [CharP F p]
theorem selected_scan (rho : Nat → F) (n : Nat) (one : rho copy=1)
    (selected : Satisfies rho CapturedValueComparison105.actualRows)
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
  have h : eval rho [(470,-1),(32752,1),(copy,1)]=rawScan rho (eval rho CapturedValueComparison105.initial) CapturedValueComparison105.entries := by
    rw [←CapturedValueComparison105.output_exact]
    exact chain_sound rho CapturedValueComparison105.initial CapturedValueComparison105.entries one CapturedValueComparison105.production_checked selected
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
end ShielddSecurity.SelectedComparisonSound159
