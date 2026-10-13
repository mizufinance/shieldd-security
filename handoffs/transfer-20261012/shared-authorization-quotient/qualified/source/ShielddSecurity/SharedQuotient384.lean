import ShielddSecurity.EncodedWordBits375
import ShielddSecurity.QuotientRows383
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedQuotient384
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem word_member :
    (CapturedWordSlots211B004.W16.slot,CapturedWordSlots211B004.W16.first)∈CapturedWordRoot213.words := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))

theorem quotient_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∀ index<4, SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (1996+index)=
      BinaryComparison100.bit (F:=F) (QuotientNumeric382.bitAt w.auth.quotient (1996+index)) := by
  have bits := EncodedWordBits375.selected_bits original c w initial senderInitial receiverInitial legal
    (CapturedWordSlots211B004.W16.slot,CapturedWordSlots211B004.W16.first) word_member (by change 1994∈SemanticWordFrame373.values; decide +kernel)
  change (∀ index<4, SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (1996+index)=
    BooleanHints207.bitValue ((encodeBits 4 w.auth.quotient)[index]?.getD false)) at bits
  intro index bound
  simpa only [QuotientNumeric382.bitAt,Nat.add_sub_cancel_left,BinaryComparison100.bit,BooleanHints207.bitValue] using bits index bound

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial)
      (fun index => CapturedFullRelation58.rowAt (179950+index)) 2 := by
  let source := EncodedWordBits375.base original w senderInitial receiverInitial
  let rho := SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  have auth := legal.2.1.2.2.2.1
  exact QuotientRows383.complete rho w.auth.quotient auth.2.2.2.2.1.2.2.1 zero (linked.trans zero) arithmetic
    (quotient_bits original c w initial senderInitial receiverInitial legal)

end ShielddSecurity.SharedQuotient384

set_option pp.all true in
#check @ShielddSecurity.SharedQuotient384.word_member
#print axioms ShielddSecurity.SharedQuotient384.word_member

set_option pp.all true in
#check @ShielddSecurity.SharedQuotient384.quotient_bits
#print axioms ShielddSecurity.SharedQuotient384.quotient_bits

set_option pp.all true in
#check @ShielddSecurity.SharedQuotient384.all_rows
#print axioms ShielddSecurity.SharedQuotient384.all_rows
