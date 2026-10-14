import ShielddSecurity.MapAssignmentValues720
import ShielddSecurity.SharedWordLimbMeaning321
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapRootBits725
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment model

theorem selected : (CapturedWordSlots211B014.W58.slot,CapturedWordSlots211B014.W58.first)∈CapturedWordRoot213.words := by
  simp only [CapturedWordRoot213.words,List.mem_cons,true_or,or_true]

theorem completed_bit (index : Nat) (before : index<255)
    (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial (20938+index)=
      BooleanHints207.bitValue ((encodeBits 255
        (representation.value (RegisteredConstructorFrame309.prepared original c w 20937)))[index]?.getD false) := by
  have point := SharedWordLimbMeaning321.encoded_point
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared original c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers original c w))
    (HeaderRegisteredConstruction310.fallback original c w)
    (LegalWordNormalization272.coherent _)
    (CapturedWordSlots211B014.W58.slot,CapturedWordSlots211B014.W58.first) selected index before
  change HeaderRegisteredConstruction310.completed original c w initial (20938+index)=
    BooleanHints207.bitValue ((encodeBits 255
      (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers original c w) 20937))[index]?.getD false) at point
  rw [LegalWordNormalization272.fixed _ 20937 (by decide)] at point
  exact point

theorem bits (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (before : index<255) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (20938+index)=
      BooleanHints207.bitValue ((encodeBits 255 (BalanceMapRoots700.selectedRoot u).val)[index]?.getD false) :=
  (MapAssignmentValues720.observed original u c w legal rkInitial authInitial initial senderInitial receiverInitial
    (20938+index) 20937 (by change 20934≤20937 ∧ 20937<21199;decide)
    (fun value : F => BooleanHints207.bitValue ((encodeBits 255 (representation.value value))[index]?.getD false))
    (completed_bit index before) (by decide)).trans
      (congrArg (fun value : F => BooleanHints207.bitValue ((encodeBits 255 (representation.value value))[index]?.getD false))
        (MapSeedValues724.selected u))

theorem root_bound (u : F) : (BalanceMapRoots700.selectedRoot u).val<TransferCore.fieldModulus :=
  ZMod.val_lt _
end ShielddSecurity.MapRootBits725

set_option pp.all true in
#check @ShielddSecurity.MapRootBits725.selected
#print axioms ShielddSecurity.MapRootBits725.selected

set_option pp.all true in
#check @ShielddSecurity.MapRootBits725.completed_bit
#print axioms ShielddSecurity.MapRootBits725.completed_bit

set_option pp.all true in
#check @ShielddSecurity.MapRootBits725.bits
#print axioms ShielddSecurity.MapRootBits725.bits

set_option pp.all true in
#check @ShielddSecurity.MapRootBits725.root_bound
#print axioms ShielddSecurity.MapRootBits725.root_bound
