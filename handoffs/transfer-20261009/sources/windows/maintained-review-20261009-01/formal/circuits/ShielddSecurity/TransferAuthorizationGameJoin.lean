import ShielddSecurity.RuntimeTransferAuthorizationOwnership
import ShielddSecurity.TransferOwnershipGame

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferAuthorizationGameJoin

open RuntimeTransferAuthorizationAk TransferOwnershipGame

variable {F J : Type} [Field F] [CharP F RuntimeTransferOwnership.modulus] [AddCommGroup J]

/-! A consumer of the maintained arbitrary-row authorization projection.
Primitive interpretations are universal, not selected ownership conclusions.
The local originalRows premise must be transported from the accepted complete
compiled witness using exact row/column certificates. The native source/owner
association, signature game and whole Transfer relation remain separate.
No certification is obtained from merely importing a retained projection. -/

structure Interpretation (codec : TransferReduction.CanonicalField F) (c : TransferSem.Crypto)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F)) where
  standardOrder : ∀ represented : J, (8 * RuntimeTransferAk.subgroupOrder) • represented = 0
  subgroup : ∀ represented : J, RuntimeTransferAk.subgroupOrder • represented = 0 →
    c.subgroup (decodePoint codec (model.coordinates represented))
  incomingHash : ∀ nk ax ay : Nat,
    nk < Scalar.modulus → ax < Scalar.modulus → ay < Scalar.modulus →
    c.hash .incomingViewingKey [nk, ax, ay] = codec.decode
      (Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
        [(nk : F), (ax : F), (ay : F)])
  multiply : ∀ scalar : Nat, ∀ represented : J,
    scalar < Scalar.order → RuntimeTransferAk.subgroupOrder • represented = 0 →
    c.mul scalar (decodePoint codec (model.coordinates represented)) =
      decodePoint codec (model.coordinates (scalar • represented))

theorem projected_answer_from_rows (codec : TransferReduction.CanonicalField F)
    (c : TransferSem.Crypto) (canonical : TransferSem.CanonicalCrypto c)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (primitive : Interpretation codec c model) (base : TransferSem.Witness) (rho : Nat → F)
    (one : rho 0 = 1)
    (rows : Satisfies rho RuntimeTransferAuthorizationOwnership.originalRows) :
    let witness := RuntimeTransferAuthorizationOwnership.projection codec rho base
    (ivkQuery witness.auth.nk witness.auth.ak).inputs =
      [witness.auth.nk] ++ TransferSem.pointFields witness.auth.ak ∧
    admittedAnswer (authorizationAnswer c canonical witness) = some witness.auth.ivk := by
  have interpreted := RuntimeTransferAuthorizationOwnership.projected_authorization_owner
    codec c base rho model primitive.standardOrder primitive.subgroup primitive.incomingHash
    primitive.multiply one rows
  exact extracted_authorization_answer c canonical _ interpreted.1

/-- Complete source classification after the local proof establishes the
ownership equation. Identical source inputs are kept as their own branch:
possessing those public source fields is not possession of the spend secret.
Different typed source inputs give a reduced alias, even if their raw field
hashes differ. No universal hash injectivity is assumed. -/
theorem projected_owner_source_alternative (codec : TransferReduction.CanonicalField F)
    (c : TransferSem.Crypto)
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (primitive : Interpretation codec c model) (faithful : FaithfulSubgroupAction c)
    (base owner : TransferSem.Witness) (rho : Nat → F) (one : rho 0 = 1)
    (rows : Satisfies rho RuntimeTransferAuthorizationOwnership.originalRows)
    (ownerScalar : TransferSem.AuthorizationScalarSem c owner)
    (sameBase : owner.sender.address.diversified =
      (RuntimeTransferAuthorizationOwnership.projection codec rho base).sender.address.diversified)
    (sameTransmission : owner.sender.address.transmission =
      (RuntimeTransferAuthorizationOwnership.projection codec rho base).sender.address.transmission)
    (ownerEquation : c.mul owner.auth.ivk owner.sender.address.diversified =
      owner.sender.address.transmission) :
    let witness := RuntimeTransferAuthorizationOwnership.projection codec rho base
    (witness.auth.nk = owner.auth.nk ∧ witness.auth.ak = owner.auth.ak) ∨
      (ivkQuery witness.auth.nk witness.auth.ak ≠ ivkQuery owner.auth.nk owner.auth.ak ∧
        witness.auth.ivk = owner.auth.ivk ∧
        c.hash .incomingViewingKey ([witness.auth.nk] ++ TransferSem.pointFields witness.auth.ak) %
          Scalar.order = owner.auth.ivk) := by
  let witness := RuntimeTransferAuthorizationOwnership.projection codec rho base
  obtain ⟨scalar, validAK, nonidentityAK, validBase, nonidentityBase, validTransmission,
      nonidentityTransmission, equation⟩ :=
    RuntimeTransferAuthorizationOwnership.projected_authorization_owner codec c base rho model
      primitive.standardOrder primitive.subgroup primitive.incomingHash primitive.multiply one rows
  by_cases same : ivkQuery witness.auth.nk witness.auth.ak = ivkQuery owner.auth.nk owner.auth.ak
  · exact Or.inl (ivk_query_injective _ _ _ _ same)
  · have hitRelation := same_address_reduced_alias c faithful witness owner scalar ownerScalar
      validBase nonidentityBase sameBase sameTransmission equation ownerEquation
    exact Or.inr ⟨same, hitRelation.1,
      (scalar_reduction_from_sem c witness scalar).trans hitRelation.1⟩

set_option pp.all true in
#check @projected_answer_from_rows
#print axioms projected_answer_from_rows
set_option pp.all true in
#check @projected_owner_source_alternative
#print axioms projected_owner_source_alternative

end ShielddSecurity.TransferAuthorizationGameJoin
