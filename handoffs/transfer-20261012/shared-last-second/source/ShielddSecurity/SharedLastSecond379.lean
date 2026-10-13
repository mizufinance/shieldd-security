import ShielddSecurity.EncodedWordBits375
import ShielddSecurity.LastSecondRows378
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedLastSecond379
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem word_member :
    (CapturedWordSlots211B007.W31.slot,CapturedWordSlots211B007.W31.first)∈CapturedWordRoot213.words := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))))))))))

theorem second_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index<17, SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (7722+index)=
      BinaryComparison100.bit (F:=F) (LastSecondNumeric377.bitAt w.volume.second (7722+index)) := by
  have bits := EncodedWordBits375.selected_bits original c w initial senderInitial receiverInitial legal
    (CapturedWordSlots211B007.W31.slot,CapturedWordSlots211B007.W31.first) word_member (by change 7609∈SemanticWordFrame373.values; decide +kernel)
  change (∀ index<17, SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (7722+index)=
    BooleanHints207.bitValue ((encodeBits 17 w.volume.second)[index]?.getD false)) at bits
  intro index bound
  simpa only [LastSecondNumeric377.bitAt,Nat.add_sub_cancel_left,BinaryComparison100.bit,BooleanHints207.bitValue] using bits index bound

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial)
      (fun index => CapturedFullRelation58.rowAt (185562+index)) 2 := by
  let source := EncodedWordBits375.base original w senderInitial receiverInitial
  let rho := SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  have volume := legal.2.1.2.2.2.2.2.2.1
  exact LastSecondRows378.complete rho w.volume.second volume.2.2.1 zero (linked.trans zero) arithmetic
    (second_bits original c w initial senderInitial receiverInitial legal)

end ShielddSecurity.SharedLastSecond379

set_option pp.all true in
#check @ShielddSecurity.SharedLastSecond379.word_member
#print axioms ShielddSecurity.SharedLastSecond379.word_member

set_option pp.all true in
#check @ShielddSecurity.SharedLastSecond379.second_bits
#print axioms ShielddSecurity.SharedLastSecond379.second_bits

set_option pp.all true in
#check @ShielddSecurity.SharedLastSecond379.all_rows
#print axioms ShielddSecurity.SharedLastSecond379.all_rows
