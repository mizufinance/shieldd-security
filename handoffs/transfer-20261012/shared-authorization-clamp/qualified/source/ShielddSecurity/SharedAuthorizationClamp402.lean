import ShielddSecurity.CapturedClampRows401
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedAuthorizationClamp402
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem comparison (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial 51208=
      BinaryComparison100.compare (F:=F) (ClampNumeric400.pairs w.auth.ivk) := by
  let source := EncodedWordBits375.base original w senderInitial receiverInitial
  let rho := SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  have bits := SharedIvkCanonical390.ivk_bits original c w initial senderInitial receiverInitial legal
  exact ClampNumeric400.semantic rho w.auth.ivk (linked.trans zero) arithmetic (by
    intro index before
    simpa only [ClampNumeric400.bitAt,ScalarCanonicalNumeric388.bitAt] using bits index before)

theorem top_quotient_bit_zero (quotient : Nat) (small : quotient<8) :
    (encodeBits 4 quotient)[3]?.getD false=false := by
  rw [UserLifecycleBits344.encoded_bit 4 quotient 3 (by decide)]
  change decide (quotient/8%2=1)=false
  rw [Nat.div_eq_of_lt small]
  rfl

theorem gate (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial 1999*
      (1-SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial 51208)=0 := by
  let rho := SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
  by_cases eight : w.auth.quotient=8
  · rw [comparison original c w initial senderInitial receiverInitial legal,
      BinaryComparison100.compare_complete (ClampNumeric400.pairs w.auth.ivk)
        (ClampNumeric400.numeric_bound w.auth.ivk (AuthorizationClamp398.quotient_eight_bound c w legal eight)),sub_self,mul_zero]
  · have scalar := legal.2.1.2.2.2.1.2.2.2.2.1
    have small : w.auth.quotient<8 := by have bounded := scalar.2.2.1; omega
    have top := SharedQuotient384.quotient_bits original c w initial senderInitial receiverInitial legal 3 (by decide)
    change rho 1999=BinaryComparison100.bit (F:=F) ((encodeBits 4 w.auth.quotient)[3]?.getD false) at top
    rw [top_quotient_bit_zero w.auth.quotient small] at top
    change rho 1999=0 at top
    change rho 1999*(1-rho 51208)=0
    rw [top,zero_mul]

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt
      (SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial)
      (fun index => CapturedFullRelation58.rowAt (180208+index)) 2 := by
  let source := EncodedWordBits375.base original w senderInitial receiverInitial
  let rho := SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  have boolean : Square (rho 51208) (rho 51208) := by
    have compared := comparison original c w initial senderInitial receiverInitial legal
    change rho 51208=BinaryComparison100.compare (F:=F) (ClampNumeric400.pairs w.auth.ivk) at compared
    rw [compared]
    exact BinaryComparison100.compare_boolean (ClampNumeric400.pairs w.auth.ivk)
  exact CapturedClampRows401.complete rho zero (linked.trans zero) arithmetic boolean
    (gate original c w initial senderInitial receiverInitial legal)

end ShielddSecurity.SharedAuthorizationClamp402

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationClamp402.comparison
#print axioms ShielddSecurity.SharedAuthorizationClamp402.comparison

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationClamp402.top_quotient_bit_zero
#print axioms ShielddSecurity.SharedAuthorizationClamp402.top_quotient_bit_zero

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationClamp402.gate
#print axioms ShielddSecurity.SharedAuthorizationClamp402.gate

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationClamp402.all_rows
#print axioms ShielddSecurity.SharedAuthorizationClamp402.all_rows
