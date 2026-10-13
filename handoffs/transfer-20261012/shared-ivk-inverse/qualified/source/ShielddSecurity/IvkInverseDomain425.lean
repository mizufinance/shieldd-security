import ShielddSecurity.AuthorizationMultiplyFrame424
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.IvkInverseDomain425
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem AuthorizationSharedFrame420B

theorem bits_map (rho : Nat → F) (start width n : Nat)
    (bits : ∀ index<width,rho (start+index)=if (encodeBits width n)[index]?.getD false then 1 else 0) :
    (List.range' start width).map rho=(encodeBits width n).map (fun bit => if bit then (1:F) else 0) := by
  apply List.ext_getElem
  · simp
  · intro index hi hj
    have before : index<width := by simpa using hi
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul]
    rw [bits index before]
    rw [List.getElem?_eq_getElem (by simpa using before),Option.getD_some]

theorem weighted_meaning (rho : Nat → F) (start width n : Nat) (small : n<2^width)
    (bits : ∀ index<width,rho (start+index)=if (encodeBits width n)[index]?.getD false then 1 else 0) :
    eval rho (weighted (List.range' start width) 1)=(n:F) := by
  rw [weighted_eval,bits_map rho start width n bits,binary_cast,encodeBits_value width n small]
  simp only [Int.cast_one,one_mul]

theorem operand_meaning (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (authInitial : Group.Point F)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original c w authInitial initial senderInitial receiverInitial)
      (weighted (List.range' 2000 252) 1)=(w.auth.ivk:F) := by
  have scalar := (AuthScalarSeed366.legal_bounds c w legal).2.1
  apply weighted_meaning _ 2000 252 w.auth.ivk scalar
  intro index before
  have bits := SharedIvkCanonical390.ivk_bits
    (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial)
    c w initial senderInitial receiverInitial legal index before
  simpa only [ScalarCanonicalNumeric388.bitAt,Nat.add_sub_cancel_left,BinaryComparison100.bit] using bits

theorem nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : (w.auth.ivk:F)≠0 := by
  have scalar := legal.2.1.2.2.2.1.2.2.2.2.1
  have small : w.auth.ivk<TransferCore.fieldModulus := lt_trans scalar.1 (by decide)
  intro zero
  have same := congrArg representation.value zero
  rw [RegistryNaturalSeed298.represented_nat w.auth.ivk small] at same
  exact scalar.2.1 same

theorem inverse_equation (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    (w.auth.ivk:F)*(w.auth.ivk:F)⁻¹=1 := mul_inv_cancel₀ (nonzero c w legal)
end ShielddSecurity.IvkInverseDomain425

set_option pp.all true in
#check @ShielddSecurity.IvkInverseDomain425.bits_map
#print axioms ShielddSecurity.IvkInverseDomain425.bits_map

set_option pp.all true in
#check @ShielddSecurity.IvkInverseDomain425.weighted_meaning
#print axioms ShielddSecurity.IvkInverseDomain425.weighted_meaning

set_option pp.all true in
#check @ShielddSecurity.IvkInverseDomain425.operand_meaning
#print axioms ShielddSecurity.IvkInverseDomain425.operand_meaning

set_option pp.all true in
#check @ShielddSecurity.IvkInverseDomain425.nonzero
#print axioms ShielddSecurity.IvkInverseDomain425.nonzero

set_option pp.all true in
#check @ShielddSecurity.IvkInverseDomain425.inverse_equation
#print axioms ShielddSecurity.IvkInverseDomain425.inverse_equation
