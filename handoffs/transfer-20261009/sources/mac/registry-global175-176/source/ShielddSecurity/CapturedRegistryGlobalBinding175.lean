import ShielddSecurity.CapturedRegistryGlobalBinding175G00
import ShielddSecurity.CapturedRegistryGlobalBinding175G01
import ShielddSecurity.CapturedRegistryGlobalBinding175G02
import ShielddSecurity.CapturedRegistryGlobalBinding175G03
import ShielddSecurity.CapturedRegistryGlobalBinding175G04
import ShielddSecurity.CapturedRegistryGlobalBinding175G05
import ShielddSecurity.CapturedRegistryGlobalBinding175G06
import ShielddSecurity.CapturedRegistryGlobalBinding175G07
import ShielddSecurity.CapturedRegistryGlobalBinding175G08
import ShielddSecurity.CapturedRegistryGlobalBinding175G09
import ShielddSecurity.CapturedRegistryGlobalBinding175G10
import ShielddSecurity.CapturedRegistryGlobalBinding175G11
import ShielddSecurity.CapturedRegistryGlobalBinding175G12
import ShielddSecurity.CapturedRegistryGlobalBinding175G13
import ShielddSecurity.CapturedRegistryGlobalBinding175G14
import ShielddSecurity.CapturedRegistryGlobalBinding175G15
import ShielddSecurity.CapturedRegistryGlobalBinding175G16
import ShielddSecurity.CapturedRegistryGlobalBinding175G17
import ShielddSecurity.CapturedRegistryGlobalBinding175G18
import ShielddSecurity.CapturedRegistryGlobalBinding175G19
import ShielddSecurity.CapturedRegistryGlobalBinding175G20
import ShielddSecurity.CapturedRegistryGlobalBinding175G21
import ShielddSecurity.CapturedRegistryGlobalBinding175G22
import ShielddSecurity.CapturedRegistryGlobalBinding175G23
import ShielddSecurity.CapturedRegistryGlobalBinding175G24
import ShielddSecurity.CapturedRegistryGlobalBinding175G25
import ShielddSecurity.CompilerIndexedSlices183
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGlobalBinding175
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41 CompilerSelectedChunks172 CompilerIndexedSlices183
noncomputable def arithmeticRows : List Row := RegistryWhole23.selectedRows.take 416
theorem count : arithmeticRows.length=416 := by
  rw [arithmeticRows,List.length_take,RegistryWhole23.row_count.1]
  rfl
noncomputable def chunks : List (List Row) := slicesAt arithmeticRows 0 [16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]
theorem partition : chunks.flatten=arithmeticRows := by
  apply CompilerIndexedSlices183.partition
  rw [count]
  decide
theorem copy_tail : RegistryWhole23.selectedRows.drop 416=[TransferPoseidonCall04Shared01.rawCopy] := by
  change (((RegistryWhole23.D0.arithmeticRows++RegistryWhole23.D1.arithmeticRows)++RegistryWhole23.tailArithmetic)++[TransferPoseidonCall04Shared01.rawCopy]).drop 416=_
  apply List.drop_left'
  have length := RegistryWhole23.row_count.1
  simp only [RegistryWhole23.selectedRows,List.length_append,List.length_singleton] at length ⊢
  omega
theorem selected_partition : arithmeticRows++[TransferPoseidonCall04Shared01.rawCopy]=RegistryWhole23.selectedRows := by
  change RegistryWhole23.selectedRows.take 416++[TransferPoseidonCall04Shared01.rawCopy]=RegistryWhole23.selectedRows
  rw [←copy_tail,List.take_append_drop]
noncomputable def copyCheck : Bool := CompilerIndexedCopyConstant178.rowCheck copy
  CapturedFullRelation58.rowAt 200770 200769 TransferPoseidonCall04Shared01.rawCopy
theorem copy_checked : copyCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho arithmeticRows := by
  rw [←partition]
  apply flatten_sound rho chunks
  change AllSatisfied rho [CapturedRegistryGlobalBinding175G00.rows,CapturedRegistryGlobalBinding175G01.rows,CapturedRegistryGlobalBinding175G02.rows,CapturedRegistryGlobalBinding175G03.rows,CapturedRegistryGlobalBinding175G04.rows,CapturedRegistryGlobalBinding175G05.rows,CapturedRegistryGlobalBinding175G06.rows,CapturedRegistryGlobalBinding175G07.rows,CapturedRegistryGlobalBinding175G08.rows,CapturedRegistryGlobalBinding175G09.rows,CapturedRegistryGlobalBinding175G10.rows,CapturedRegistryGlobalBinding175G11.rows,CapturedRegistryGlobalBinding175G12.rows,CapturedRegistryGlobalBinding175G13.rows,CapturedRegistryGlobalBinding175G14.rows,CapturedRegistryGlobalBinding175G15.rows,CapturedRegistryGlobalBinding175G16.rows,CapturedRegistryGlobalBinding175G17.rows,CapturedRegistryGlobalBinding175G18.rows,CapturedRegistryGlobalBinding175G19.rows,CapturedRegistryGlobalBinding175G20.rows,CapturedRegistryGlobalBinding175G21.rows,CapturedRegistryGlobalBinding175G22.rows,CapturedRegistryGlobalBinding175G23.rows,CapturedRegistryGlobalBinding175G24.rows,CapturedRegistryGlobalBinding175G25.rows]
  exact ⟨CapturedRegistryGlobalBinding175G00.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G01.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G02.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G03.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G04.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G05.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G06.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G07.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G08.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G09.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G10.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G11.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G12.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G13.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G14.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G15.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G16.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G17.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G18.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G19.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G20.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G21.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G22.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G23.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G24.sound rho satisfied,⟨CapturedRegistryGlobalBinding175G25.sound rho satisfied,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho RegistryWhole23.selectedRows := by
  have copying:=CompilerIndexedCopyConstant178.row_sound copy CapturedFullRelation58.rowAt 200770 200769
    TransferPoseidonCall04Shared01.rawCopy copy_checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
  intro row member
  rw [←selected_partition] at member
  rcases List.mem_append.mp member with member|member
  · exact arithmetic_sound rho satisfied row member
  · exact copying row member
end ShielddSecurity.CapturedRegistryGlobalBinding175

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.arithmeticRows
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.count
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.count
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.chunks
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.chunks
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.partition
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.copy_tail
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.copy_tail
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.selected_partition
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.selected_partition
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.copyCheck
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.copyCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.copy_checked
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.copy_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.arithmetic_sound
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.arithmetic_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175.sound
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175.sound
