import ShielddSecurity.CapturedHighLimbShared124
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CapturedAssertions50B0004
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedHighZero126Data
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def delta : Linear := weighted CapturedRegistryHighLimb120.leftColumns 1++weighted CapturedRegistryHighLimb120.rightColumns (-1)
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.delta
#print axioms ShielddSecurity.CapturedHighZero126Data.delta
noncomputable def arithmeticRows : List Row := @AR@
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.arithmeticRows
#print axioms ShielddSecurity.CapturedHighZero126Data.arithmeticRows
noncomputable def actualRows : List Row := @AS@
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.actualRows
#print axioms ShielddSecurity.CapturedHighZero126Data.actualRows
noncomputable def arithmeticCheck : Bool := CompilerRowSlice63.check CapturedArithmetic45B0048.block.actual 440 4 arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.arithmeticCheck
#print axioms ShielddSecurity.CapturedHighZero126Data.arithmeticCheck
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.arithmetic_checked
#print axioms ShielddSecurity.CapturedHighZero126Data.arithmetic_checked
noncomputable def assertionCheck : Bool := CompilerRowSlice63.check CapturedAssertions50B0004.block.actual 45 3 actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.assertionCheck
#print axioms ShielddSecurity.CapturedHighZero126Data.assertionCheck
theorem assertion_checked : assertionCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.assertion_checked
#print axioms ShielddSecurity.CapturedHighZero126Data.assertion_checked
theorem arithmetic_position (index : Nat) (bound : index<4) :
    CapturedFullArithmetic52.rowAt (11032+index)=arithmeticRows[index]? := by
  have leaf:=CompilerRowSlice63.position CapturedArithmetic45B0048.block.actual 440 4 arithmeticRows arithmetic_checked index bound
  have h0 : 11032+index<83708 := by omega
  have h1 : 11032+index<28302 := by omega
  have h2 : 11032+index<14381 := by omega
  have h3 : ¬11032+index<6760 := by omega
  have h4 : ¬11032+index-6760<3832 := by omega
  have h5 : 11032+index-6760-3832<2158 := by omega
  have h6 : 11032+index-6760-3832<1332 := by omega
  have h7 : 11032+index-6760-3832<924 := by omega
  have h8 : 11032+index-6760-3832<512 := by omega
  have same : 11032+index-6760-3832=440+index := by omega
  simp only [CapturedFullArithmetic52.rowAt,CapturedFullArithmetic52.block,
    CompilerArithmeticBlock44.append,if_pos h0,if_pos h1,if_pos h2]
  simp only [CapturedArithmetic52G00.block,CompilerArithmeticBlock44.append,
    if_neg h3,if_neg h4,if_pos h5,if_pos h6,if_pos h7,if_pos h8,same]
  exact leaf
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.arithmetic_position
#print axioms ShielddSecurity.CapturedHighZero126Data.arithmetic_position
theorem assertion_position (index : Nat) (bound : index<3) :
    CapturedFullRelation58.rowAt (179023+index)=actualRows[index]? := by
  have sum : 179023+index=177954+(1069+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1069+index) (by omega)]
  change (if 1069+index<12288 then _ else _)=_
  rw [if_pos (show 1069+index<12288 by omega)]
  change (if 1069+index<4096 then _ else _)=_
  rw [if_pos (show 1069+index<4096 by omega)]
  change (if 1069+index<2048 then _ else _)=_
  rw [if_pos (show 1069+index<2048 by omega)]
  change (if 1069+index<1024 then _ else _)=_
  rw [if_neg (show ¬1069+index<1024 by omega)]
  change (if 1069+index-1024<512 then _ else _)=_
  rw [if_pos (show 1069+index-1024<512 by omega)]
  change (if 1069+index-1024<256 then _ else _)=_
  rw [if_pos (show 1069+index-1024<256 by omega)]
  have same : 1069+index-1024=45+index := by omega
  change CapturedAssertions50B0004.block.actual (1069+index-1024)=_
  rw [same]
  exact CompilerRowSlice63.position CapturedAssertions50B0004.block.actual 45 3 actualRows assertion_checked index bound
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126Data.assertion_position
#print axioms ShielddSecurity.CapturedHighZero126Data.assertion_position
end ShielddSecurity.CapturedHighZero126Data
