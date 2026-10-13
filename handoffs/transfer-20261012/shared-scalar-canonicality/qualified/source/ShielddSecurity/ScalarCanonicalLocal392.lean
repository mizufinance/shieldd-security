import ShielddSecurity.ScalarCanonicalNumeric388
import ShielddSecurity.CompilerRenamingChecks05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ScalarCanonicalLocal392
open Compiler CompilerArithmeticTransport41 ComparisonCertificate101 BinaryComparison100 ScalarCanonicalNumeric388
variable {F : Type} [Field F] [CharP F p]
theorem semantic_rows (rho : Nat → F) (n : Nat) (bound : n<TransferCore.scalarOrder) (one : rho copy=1)
    (satisfied : Satisfies rho ScalarCanonicalCapture387.actualRows)
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
  have h:=chain_sound rho ScalarCanonicalCapture387.initial ScalarCanonicalCapture387.entries one ScalarCanonicalCapture387.production_checked satisfied
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
end ShielddSecurity.ScalarCanonicalLocal392
set_option pp.all true in
#check @ShielddSecurity.ScalarCanonicalLocal392.semantic_rows
#print axioms ShielddSecurity.ScalarCanonicalLocal392.semantic_rows
