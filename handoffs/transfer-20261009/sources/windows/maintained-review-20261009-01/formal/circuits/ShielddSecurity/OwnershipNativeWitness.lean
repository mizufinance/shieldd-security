import ShielddSecurity.RuntimeTransferOwnershipIvk
import ShielddSecurity.GroupNativeSdk

set_option maxHeartbeats 400000

namespace ShielddSecurity.OwnershipNativeWitness

/-- Coverage is a global functional contract of canonical native Fr parsing
and native subgroup parsing, for every legal value. It is independent of rho
and of the circuit's output. The actual arbitrary rows derive the scalar hash
decomposition and legal sender point; native input reader bindings follow. -/
theorem actual_native_witness {F : Type} [Field F]
    [CharP F RuntimeTransferOwnership.modulus]
    {E S R K Q J : Type} [AddCommGroup J]
    (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (decoder : GroupByteCodec.BERead (F := F))
    (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
    (upstream : GroupNativeSdk.Sdk fq fr (RuntimeTransferOwnership.coefficientD : F) model
      (E := E) (S := S) (R := R) (K := K))
    (nativeScalarCoverage : ∀ n : Nat, n < Scalar.order →
      ∃ scalar : R, fr.integer scalar = n)
    (nativePointCoverage : ∀ represented : J,
      RuntimeTransferAk.subgroupOrder • represented = 0 →
      ∃ point : S, upstream.embed (upstream.promote point) = represented)
    (standardOrder : ∀ represented : J,
      (8 * RuntimeTransferAk.subgroupOrder) • represented = 0)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (satisfied : Satisfies rho RuntimeTransferOwnershipIvk.rawRows) :
    ∃ q r : Nat, ∃ sender : S, ∃ scalar : R,
      q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧ q * Scalar.order + r < Scalar.modulus ∧
      ((q * Scalar.order + r : Nat) : F) =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          (RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho)) ∧
      fr.integer scalar = r ∧ upstream.embed (upstream.promote sender) ≠ 0 ∧
      GroupNativeSdk.readFq fq decoder (upstream.x sender) =
        some (RuntimeTransferOwnership.base rho).x ∧
      GroupNativeSdk.readFq fq decoder (upstream.y sender) =
        some (RuntimeTransferOwnership.base rho).y ∧
      GroupNativeSdk.readScalar fq fr decoder scalar =
        some (eval rho RuntimeTransferReduction.consumer) ∧
      RuntimeTransferOwnership.target rho =
        model.coordinates (upstream.embed (upstream.multiply (upstream.promote sender) scalar)) := by
  have ownershipSat : Satisfies rho RuntimeTransferSenderOwnership.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have ivkSat : Satisfies rho RuntimeTransferIvk.originalRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  obtain ⟨q, r, qBound, positive, rBound, noWrap, _, _, hash, consumer⟩ :=
    RuntimeTransferIvk.actual_hash_reduction rho one four ivkSat
  obtain ⟨senderBase, coordinates, subgroup, nonidentity, target⟩ :=
    RuntimeTransferSenderOwnership.actual_sender_ownership rho one four codec model
      standardOrder ownershipSat
  have bitSat : Satisfies rho RuntimeTransferOwnership.bitRows := by
    intro row member
    exact ownershipSat row (List.mem_append_left _
      (List.mem_append_right _ (List.mem_append_left _ member)))
  have bitValue := RuntimeTransferOwnershipIvk.decoded_scalar rho r rBound consumer bitSat
  rw [bitValue] at target
  obtain ⟨scalar, scalarInteger⟩ := nativeScalarCoverage r rBound
  obtain ⟨sender, pointEmbedding⟩ := nativePointCoverage senderBase subgroup
  have pointRole : model.coordinates (upstream.embed (upstream.promote sender)) =
      RuntimeTransferOwnership.base rho := by
    rw [pointEmbedding]
    exact coordinates
  have xValue : (fq.integer (upstream.x sender) : F) =
      (RuntimeTransferOwnership.base rho).x :=
    congrArg Group.Point.x ((upstream.coordinates sender).symm.trans pointRole)
  have yValue : (fq.integer (upstream.y sender) : F) =
      (RuntimeTransferOwnership.base rho).y :=
    congrArg Group.Point.y ((upstream.coordinates sender).symm.trans pointRole)
  have readX : GroupNativeSdk.readFq fq decoder (upstream.x sender) =
      some (RuntimeTransferOwnership.base rho).x := by
    rw [GroupNativeSdk.fq_read, xValue]
  have readY : GroupNativeSdk.readFq fq decoder (upstream.y sender) =
      some (RuntimeTransferOwnership.base rho).y := by
    rw [GroupNativeSdk.fq_read, yValue]
  have readScalar : GroupNativeSdk.readScalar fq fr decoder scalar =
      some (eval rho RuntimeTransferReduction.consumer) := by
    rw [GroupNativeSdk.scalar_read, scalarInteger, consumer]
  have nativeNonidentity : upstream.embed (upstream.promote sender) ≠ 0 := by
    rw [pointEmbedding]
    exact nonidentity
  have nativeTarget : RuntimeTransferOwnership.target rho =
      model.coordinates (upstream.embed (upstream.multiply (upstream.promote sender) scalar)) := by
    rw [upstream.multiplyEmbedding, scalarInteger, pointEmbedding]
    exact target
  exact ⟨q, r, sender, scalar, qBound, positive, rBound, noWrap, hash,
    scalarInteger, nativeNonidentity, readX, readY, readScalar, nativeTarget⟩

set_option pp.all true in
#check @actual_native_witness
#print axioms actual_native_witness

end ShielddSecurity.OwnershipNativeWitness
