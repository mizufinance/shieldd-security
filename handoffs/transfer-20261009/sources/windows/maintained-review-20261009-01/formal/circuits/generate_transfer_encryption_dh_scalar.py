"""Reuse an accepted EPK scalar in one qualified variable-base DH occurrence.

The generated bit-list check concerns actual imported definitions. Integer
positivity, subgroup-order bound and private-input meaning come from EPK rows.
Input key representation and full-matrix/caller/native joins remain separate.
"""
from .transfer_encryption_dh import join_epk
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def generate(full_occurrence, accepted_epk):
    joined = join_epk(full_occurrence, accepted_epk)
    role, slot = joined['role'], joined['slot']
    scalar = joined['scalar']
    if scalar[0] != 'source' or scalar[1][0] != 1:
        raise relation.RelationError('DH scalar renderer exact private witness required')
    scalar_column = scalar[1][1] + 3
    scope = 2 + slot
    epk = f'TransferEpkScope{scope}Relation'
    mapping = f'RuntimeTransferEpk{scope}RenamingMap'
    loop = f'RuntimeTransferEncryptionDh{role}Loop'
    name = f'RuntimeTransferEncryptionDh{role}Scalar'
    private = linear(((scalar_column, 1),))
    output = f'''import ShielddSecurity.EncryptionDhScalar
import ShielddSecurity.{epk}
import ShielddSecurity.{loop}

namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def privateValue : Linear := {private}

theorem bits_checked : RuntimeTransferEpk0Canonical.bits.map
    (RowRenaming.linear {mapping}.columns) = {loop}.bits := by decide

theorem scalar_role {{F : Type}} [Field F] (rho : Nat → F) :
    binary (ScalarBits.decodeBits rho {loop}.bits) = {epk}.scalar rho := by
  change _ = binary (ScalarBits.decodeBits (fun column => rho ({mapping}.columns column))
    RuntimeTransferEpk0Canonical.bits)
  exact (EncryptionDhScalar.scalar_agrees rho {mapping}.columns
    RuntimeTransferEpk0Canonical.bits {loop}.bits bits_checked).symm

theorem actual_scalar_multiplication {{F J : Type}} [Field F]
    [CharP F RuntimeTransferRnkLoop.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F))
    (generator inputBase : J) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferRnkLoop.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (baseRole : {loop}.base rho = model.coordinates inputBase)
    (epkSatisfied : Satisfies rho {epk}.rows)
    (dhSatisfied : Satisfies rho {loop}.rawRows) :
    0 < {epk}.scalar rho ∧ {epk}.scalar rho < Scalar.order ∧
      ({epk}.scalar rho : F) = eval rho privateValue ∧
      {loop}.output rho = model.coordinates ({epk}.scalar rho • inputBase) := by
  have scalar := {epk}.sound model rho generator one four imaginary nonSquare
    imaginarySquare baseMeaning epkSatisfied
  have result := {loop}.actual_multiplication rho one four codec model inputBase baseRole dhSatisfied
  rw [scalar_role rho] at result
  have input : ({epk}.scalar rho : F) = eval rho privateValue := by
    simpa only [privateValue, eval, Int.cast_one, one_mul, add_zero] using scalar.2.2.1
  exact ⟨scalar.1, scalar.2.1, input, result⟩
#print axioms bits_checked
#print axioms scalar_role
#print axioms actual_scalar_multiplication
end ShielddSecurity.{name}
'''
    return name, _signature_audits(output)
