import ShielddSecurity.FixedFamilyBindings551
import ShielddSecurity.AuthorizationFixedInitial499
import ShielddSecurity.FixedFamilyInitial555F00
import ShielddSecurity.FixedFamilyInitial555F01
import ShielddSecurity.FixedFamilyInitial555F02
import ShielddSecurity.FixedFamilyInitial555F03
import ShielddSecurity.FixedFamilyInitial555F04
import ShielddSecurity.FixedFamilyInitial555F05
import ShielddSecurity.FixedFamilyInitial555F06
import ShielddSecurity.FixedFamilyInitial555F07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyInitial554
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open FixedFamilyBindings551 (assignment)
open FixedFamilyLayout545
open AuthorizationFixedSeed487 (window)
attribute [local irreducible] assignment SemanticWordFrame373.assignment model
theorem family0 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+5040+i)) 2 := by
  apply (FixedFamilyInitial555F00.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨0,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 5183=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 4931=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 4932=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F00.table_points.1,
    FixedFamilyInitial555F00.table_points.2.1,FixedFamilyInitial555F00.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family0
#print axioms family0
theorem family1 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+6443+i)) 2 := by
  apply (FixedFamilyInitial555F01.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨1,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 6587=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 6335=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 6336=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F01.table_points.1,
    FixedFamilyInitial555F01.table_points.2.1,FixedFamilyInitial555F01.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family1
#print axioms family1
theorem family2 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+8574+i)) 2 := by
  apply (FixedFamilyInitial555F02.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨2,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 8804=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 8552=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 8553=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F02.table_points.1,
    FixedFamilyInitial555F02.table_points.2.1,FixedFamilyInitial555F02.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family2
#print axioms family2
theorem family3 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+10114+i)) 2 := by
  apply (FixedFamilyInitial555F03.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨3,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 10336=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 10084=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 10085=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F03.table_points.1,
    FixedFamilyInitial555F03.table_points.2.1,FixedFamilyInitial555F03.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family3
#print axioms family3
theorem family4 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+11654+i)) 2 := by
  apply (FixedFamilyInitial555F04.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨4,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 11864=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 11612=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 11613=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F04.table_points.1,
    FixedFamilyInitial555F04.table_points.2.1,FixedFamilyInitial555F04.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family4
#print axioms family4
theorem family5 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+13676+i)) 2 := by
  apply (FixedFamilyInitial555F05.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨5,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 13882=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 13630=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 13631=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F05.table_points.1,
    FixedFamilyInitial555F05.table_points.2.1,FixedFamilyInitial555F05.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family5
#print axioms family5
theorem family6 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+14942+i)) 2 := by
  apply (FixedFamilyInitial555F06.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨6,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 15144=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 14892=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 14893=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F06.table_points.1,
    FixedFamilyInitial555F06.table_points.2.1,FixedFamilyInitial555F06.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family6
#print axioms family6
theorem family7 (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+16208+i)) 2 := by
  apply (FixedFamilyInitial555F07.rows_iff _
    (FixedFamilyBindings551.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (FixedFamilyBindings551.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)).mpr
  let family : Fin 8 := ⟨7,by decide⟩
  have pair := AuthorizationFixedLocal493.bits (scalar w family) 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (window (scalar w family) 0).low=(encodeBits 252 (scalar w family))[0]?.getD false at low
  change (window (scalar w family) 0).high=(encodeBits 252 (scalar w family))[1]?.getD false at high
  have lowBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  have highBit := FixedFamilyBindings551.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial family 1 (by decide)
  have output := FixedFamilyBindings551.point original c w legal rkInitial authInitial initial senderInitial receiverInitial family 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 16406=(window (scalar w family) 0).output at output
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 16154=_ at lowBit
  change assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 16155=_ at highBit
  rw [output,lowBit,highBit,←low,←high,FixedFamilyInitial555F07.table_points.1,
    FixedFamilyInitial555F07.table_points.2.1,FixedFamilyInitial555F07.table_points.2.2]
  exact AuthorizationFixedInitial499.first_output (scalar w family)
set_option pp.all true in
#check @family7
#print axioms family7
end ShielddSecurity.FixedFamilyInitial554
