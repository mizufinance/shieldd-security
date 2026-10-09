"""Join actual DH scalar/row results to the owned native scalar reader.

The source publisher must supply a qualified role and EPK slot from the actual
five scalar join packet. The input-base and generator operand bindings remain
explicit; no desired native/circuit multiplication output is an input premise.
"""
from .generate_hash_round import _signature_audits


def generate(role, slot):
    if type(role) is not int or type(slot) is not int or not 0 <= role < 5:
        raise ValueError('one actual DH role required')
    if slot != (0 if role <= 1 else role - 1):
        raise ValueError('actual detection/core/ext EPK slot association required')
    epk = f'TransferEpkScope{2 + slot}Relation'
    scalar = f'RuntimeTransferEncryptionDh{role}Scalar'
    loop = f'RuntimeTransferEncryptionDh{role}Loop'
    name = f'RuntimeTransferEncryptionDh{role}Native'
    text = f'''import ShielddSecurity.EncryptionDhNative
import ShielddSecurity.{scalar}

namespace ShielddSecurity.{name}
set_option maxHeartbeats 250000

theorem native_same_assignment {{F J : Type}} [Field F]
    [CharP F RuntimeTransferRnkLoop.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec)
    (model : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F))
    (generator inputBase : J) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferRnkLoop.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (baseRole : {loop}.base rho = model.coordinates inputBase)
    (epkSatisfied : Satisfies rho {epk}.rows)
    (dhSatisfied : Satisfies rho {loop}.rawRows) :
    {loop}.output rho = EncryptionDhNative.multiply writer
      (RuntimeTransferRnkLoop.coefficientD : F) ({loop}.base rho)
      (eval rho {scalar}.privateValue) := by
  have facts := {scalar}.actual_scalar_multiplication rho one four codec model
    generator inputBase imaginary nonSquare imaginarySquare baseMeaning baseRole epkSatisfied dhSatisfied
  have two : (2 : F) ≠ 0 := by
    intro zero
    apply four
    calc
      (4 : F) = (2 : F) + 2 := by ring
      _ = 0 := by rw [zero, zero, zero_add]
  rw [facts.2.2.2, baseRole, ← facts.2.2.1]
  exact (EncryptionDhNative.canonical_multiply_coordinates codec writer
    (RuntimeTransferRnkLoop.coefficientD : F) imaginary model nonSquare imaginarySquare
    two inputBase ({epk}.scalar rho) facts.2.1).symm

theorem native_output_nonzero {{F J : Type}} [Field F]
    [CharP F RuntimeTransferRnkLoop.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F))
    (generator inputBase : J) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferRnkLoop.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (baseRole : {loop}.base rho = model.coordinates inputBase)
    (standardPrime : Nat.Prime Scalar.order)
    (subgroup : Scalar.order • inputBase = 0) (nonidentity : inputBase ≠ 0)
    (epkSatisfied : Satisfies rho {epk}.rows)
    (dhSatisfied : Satisfies rho {loop}.rawRows) :
    {loop}.output rho ≠ Group.identityPoint := by
  have facts := {scalar}.actual_scalar_multiplication rho one four codec model
    generator inputBase imaginary nonSquare imaginarySquare baseMeaning baseRole epkSatisfied dhSatisfied
  have nonzero := GroupNativeSubgroupMultiply.canonical_input_multiple_nonzero
    standardPrime inputBase subgroup nonidentity ({epk}.scalar rho) facts.1 facts.2.1
  rw [facts.2.2.2, ← model.identity]
  intro zero
  exact nonzero (model.injective zero)

theorem native_output_inverse {{F J : Type}} [Field F]
    [CharP F RuntimeTransferRnkLoop.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F))
    (generator inputBase : J) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferRnkLoop.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (baseRole : {loop}.base rho = model.coordinates inputBase)
    (standardPrime : Nat.Prime Scalar.order)
    (subgroup : Scalar.order • inputBase = 0) (nonidentity : inputBase ≠ 0)
    (epkSatisfied : Satisfies rho {epk}.rows)
    (dhSatisfied : Satisfies rho {loop}.rawRows) :
    ({loop}.output rho).x * (({loop}.output rho).x)⁻¹ = 1 := by
  have facts := {scalar}.actual_scalar_multiplication rho one four codec model
    generator inputBase imaginary nonSquare imaginarySquare baseMeaning baseRole epkSatisfied dhSatisfied
  rw [facts.2.2.2]
  exact GroupNativeSubgroupMultiply.canonical_input_multiple_inverse
    (RuntimeTransferRnkLoop.coefficientD : F) model standardPrime inputBase subgroup nonidentity
    ({epk}.scalar rho) facts.1 facts.2.1
#print axioms native_same_assignment
#print axioms native_output_nonzero
#print axioms native_output_inverse
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
