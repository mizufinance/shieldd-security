import ShielddSecurity.CapturedNextHighLimb133
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CapturedAssertions50B0005
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextHighZero137Data
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def delta : Linear := weighted CapturedNextHighLimb133.leftColumns 1++weighted CapturedNextHighLimb133.rightColumns (-1)
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.delta
#print axioms ShielddSecurity.CapturedNextHighZero137Data.delta
noncomputable def arithmeticRows : List Row := @AR@
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.arithmeticRows
#print axioms ShielddSecurity.CapturedNextHighZero137Data.arithmeticRows
noncomputable def actualRows : List Row := @AS@
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.actualRows
#print axioms ShielddSecurity.CapturedNextHighZero137Data.actualRows
noncomputable def arithmeticCheck : Bool := CompilerRowSlice63.check CapturedArithmetic45B0048.block.actual 448 4 arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.arithmeticCheck
#print axioms ShielddSecurity.CapturedNextHighZero137Data.arithmeticCheck
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.arithmetic_checked
#print axioms ShielddSecurity.CapturedNextHighZero137Data.arithmetic_checked
noncomputable def assertionCheck : Bool := CompilerRowSlice63.check CapturedAssertions50B0005.block.actual 53 3 actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.assertionCheck
#print axioms ShielddSecurity.CapturedNextHighZero137Data.assertionCheck
theorem assertion_checked : assertionCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.assertion_checked
#print axioms ShielddSecurity.CapturedNextHighZero137Data.assertion_checked
theorem arithmetic_position (index : Nat) (bound : index<4) :
    CapturedFullArithmetic52.rowAt (11040+index)=arithmeticRows[index]? := by
  have leaf:=CompilerRowSlice63.position CapturedArithmetic45B0048.block.actual 448 4 arithmeticRows arithmetic_checked index bound
  have same : CapturedFullArithmetic52.rowAt (11040+index)=
      CapturedArithmetic45B0048.block.actual (448+index) := by
    have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals rfl
  exact same.trans leaf
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.arithmetic_position
#print axioms ShielddSecurity.CapturedNextHighZero137Data.arithmetic_position
theorem assertion_position (index : Nat) (bound : index<3) :
    CapturedFullRelation58.rowAt (179287+index)=actualRows[index]? := by
  have sum : 179287+index=177954+(1333+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1333+index) (by omega)]
  change (if 1333+index<12288 then _ else _)=_
  rw [if_pos (show 1333+index<12288 by omega)]
  change (if 1333+index<4096 then _ else _)=_
  rw [if_pos (show 1333+index<4096 by omega)]
  change (if 1333+index<2048 then _ else _)=_
  rw [if_pos (show 1333+index<2048 by omega)]
  change (if 1333+index<1024 then _ else _)=_
  rw [if_neg (show ¬1333+index<1024 by omega)]
  change (if 1333+index-1024<512 then _ else _)=_
  rw [if_pos (show 1333+index-1024<512 by omega)]
  change (if 1333+index-1024<256 then _ else _)=_
  rw [if_neg (show ¬1333+index-1024<256 by omega)]
  have same : 1333+index-1024-256=53+index := by omega
  change CapturedAssertions50B0005.block.actual (1333+index-1024-256)=_
  rw [same]
  exact CompilerRowSlice63.position CapturedAssertions50B0005.block.actual 53 3 actualRows assertion_checked index bound
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero137Data.assertion_position
#print axioms ShielddSecurity.CapturedNextHighZero137Data.assertion_position
end ShielddSecurity.CapturedNextHighZero137Data
