import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.ComparisonComposition103
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CanonicalComparisonSlices218
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ComparisonCertificate101
theorem slice (start count : Nat) (rows : List Row)
 (checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt start count rows=true)
 (bound : start+count≤177954) :
 ∀ row∈rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row := by
 intro row member
 obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
 obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
 have length:rows.length=count := CompilerRowSlice63.count _ start count rows checked
 have ib:index<count := by omega
 refine ⟨start+index,by omega,?_⟩
 rw [CompilerRowSlice63.position _ start count rows checked index ib]
 exact found
theorem append (left right : List Entry)
 (a : ∀ row∈left.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row)
 (b : ∀ row∈right.flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row) :
 ∀ row∈(left++right).flatMap Entry.rows,∃ index<177954,CapturedFullArithmetic52.rowAt index=some row := by
 intro row member
 rw [List.flatMap_append] at member
 rcases List.mem_append.mp member with member|member
 · exact a row member
 · exact b row member
end ShielddSecurity.CanonicalComparisonSlices218

set_option pp.all true in
#check @ShielddSecurity.CanonicalComparisonSlices218.slice
#print axioms ShielddSecurity.CanonicalComparisonSlices218.slice
set_option pp.all true in
#check @ShielddSecurity.CanonicalComparisonSlices218.append
#print axioms ShielddSecurity.CanonicalComparisonSlices218.append
