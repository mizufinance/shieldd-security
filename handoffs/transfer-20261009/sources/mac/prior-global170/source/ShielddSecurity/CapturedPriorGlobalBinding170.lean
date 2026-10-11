import ShielddSecurity.CapturedPriorPack179Pilot64
import ShielddSecurity.CapturedPriorGlobalBinding170G000
import ShielddSecurity.CapturedPriorGlobalBinding170G001
import ShielddSecurity.CapturedPriorGlobalBinding170G002
import ShielddSecurity.CapturedPriorGlobalBinding170G003
import ShielddSecurity.CapturedPriorGlobalBinding170G004
import ShielddSecurity.CompilerSelectedChunks172
import ShielddSecurity.CapturedCall04GlobalBinding168
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedPriorGlobalBinding170
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 CompilerSelectedChunks172
noncomputable def headRows : List Row := CapturedPriorRows16Chunk01.rows.take 322
theorem count : headRows.length=322 := by
  rw [headRows,List.length_take,CapturedPriorRows16Chunk01.row_count]
  decide
noncomputable def chunks : List (List Row) := slices headRows [64,64,64,64,64,2]
theorem partition : chunks.flatten=headRows := by
  rw [chunks,slices_flatten]
  have total : [64,64,64,64,64,2].sum=322 := by decide +kernel
  rw [total]
  apply List.take_of_length_le
  exact Nat.le_of_eq count
theorem prior_partition : headRows++CapturedInitial73419Completion01.callRows =
    CapturedPriorRows16Frame01.capturedPriorRows := by
  change CapturedPriorRows16Chunk01.rows.take 322++
    ((((CapturedPriorRows16Chunk01.rows.drop 322++CapturedPriorRows16Chunk02.rows)++
      CapturedPriorRows16Chunk03.rows)++CapturedPriorRows16Chunk04.rows)++CapturedPriorRows16Chunk05.rows) =
    (((CapturedPriorRows16Chunk01.rows++CapturedPriorRows16Chunk02.rows)++
      CapturedPriorRows16Chunk03.rows)++CapturedPriorRows16Chunk04.rows)++CapturedPriorRows16Chunk05.rows
  simp only [←List.append_assoc,List.take_append_drop]
variable {F : Type} [Field F] [CharP F p]
theorem head_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho headRows := by
  rw [←partition]
  apply flatten_sound rho chunks
  change AllSatisfied rho [CapturedPriorPack179Pilot64.rows,CapturedPriorGlobalBinding170G000.rows,CapturedPriorGlobalBinding170G001.rows,CapturedPriorGlobalBinding170G002.rows,CapturedPriorGlobalBinding170G003.rows,CapturedPriorGlobalBinding170G004.rows]
  exact ⟨CapturedPriorPack179Pilot64.sound rho satisfied,⟨CapturedPriorGlobalBinding170G000.sound rho satisfied,⟨CapturedPriorGlobalBinding170G001.sound rho satisfied,⟨CapturedPriorGlobalBinding170G002.sound rho satisfied,⟨CapturedPriorGlobalBinding170G003.sound rho satisfied,⟨CapturedPriorGlobalBinding170G004.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho CapturedPriorRows16Frame01.capturedPriorRows := by
  intro row member
  rw [←prior_partition] at member
  rcases List.mem_append.mp member with member|member
  · exact head_sound rho satisfied row member
  · exact CapturedCall04GlobalBinding168.sound rho satisfied row member
end ShielddSecurity.CapturedPriorGlobalBinding170

set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.headRows
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.headRows
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.count
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.count
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.chunks
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.partition
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.prior_partition
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.prior_partition
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.head_sound
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.head_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorGlobalBinding170.sound
#print axioms ShielddSecurity.CapturedPriorGlobalBinding170.sound
