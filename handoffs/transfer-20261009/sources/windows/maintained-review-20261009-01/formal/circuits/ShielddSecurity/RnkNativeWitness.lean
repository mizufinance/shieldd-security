import ShielddSecurity.RuntimeTransferRnkIvk
import ShielddSecurity.GroupNativeSdk

set_option maxHeartbeats 400000

namespace ShielddSecurity.RnkNativeWitness

/-- Global canonical parsing coverage supplies native operand values after
the actual RNK/Ivk rows derive the scalar and subgroup base. No premise
identifies a per-assignment reader or assumes the DH output. -/
theorem actual_native_witness {F : Type} [Field F]
    [CharP F RuntimeTransferRnkLoop.modulus]
    {E S R K Q J : Type} [AddCommGroup J]
    (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (decoder : GroupByteCodec.BERead (F := F))
    (model : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F))
    (upstream : GroupNativeSdk.Sdk fq fr (RuntimeTransferRnkLoop.coefficientD : F) model
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
    (satisfied : Satisfies rho RuntimeTransferRnkIvk.rawRows) :
    ∃ q r : Nat, ∃ input : S, ∃ scalar : R,
      q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧ q * Scalar.order + r < Scalar.modulus ∧
      ((q * Scalar.order + r : Nat) : F) =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          (RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho)) ∧
      fr.integer scalar = r ∧ upstream.embed (upstream.promote input) ≠ 0 ∧
      GroupNativeSdk.readFq fq decoder (upstream.x input) =
        some (RuntimeTransferRnkLoop.base rho).x ∧
      GroupNativeSdk.readFq fq decoder (upstream.y input) =
        some (RuntimeTransferRnkLoop.base rho).y ∧
      GroupNativeSdk.readScalar fq fr decoder scalar =
        some (eval rho RuntimeTransferReduction.consumer) ∧
      (⟨eval rho [(3763, (1 : Int))], eval rho [(3764, (1 : Int))]⟩ : Group.Point F) =
        model.coordinates (upstream.embed (upstream.multiply (upstream.promote input) scalar)) := by
  have baseSat : Satisfies rho RuntimeTransferRnkBase.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have ivkSat : Satisfies rho RuntimeTransferIvk.originalRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  obtain ⟨q, r, qBound, positive, rBound, noWrap, _, _, hash, consumer⟩ :=
    RuntimeTransferIvk.actual_hash_reduction rho one four ivkSat
  obtain ⟨represented, coordinates, subgroup, nonidentity, target⟩ :=
    RuntimeTransferRnkBase.actual_rnk_multiplication rho one four codec model standardOrder baseSat
  have bitSat : Satisfies rho RuntimeTransferRnkLoop.bitRows := by
    intro row member
    exact baseSat row (List.mem_append_left _ (List.mem_append_right _ member))
  have bitValue := RuntimeTransferRnkIvk.decoded_scalar rho r rBound consumer bitSat
  rw [bitValue, RuntimeTransferRnkLoop.captured_output_role rho] at target
  obtain ⟨scalar, scalarInteger⟩ := nativeScalarCoverage r rBound
  obtain ⟨input, pointEmbedding⟩ := nativePointCoverage represented subgroup
  have pointRole : model.coordinates (upstream.embed (upstream.promote input)) =
      RuntimeTransferRnkLoop.base rho := by
    rw [pointEmbedding]
    exact coordinates
  have xValue : (fq.integer (upstream.x input) : F) =
      (RuntimeTransferRnkLoop.base rho).x :=
    congrArg Group.Point.x ((upstream.coordinates input).symm.trans pointRole)
  have yValue : (fq.integer (upstream.y input) : F) =
      (RuntimeTransferRnkLoop.base rho).y :=
    congrArg Group.Point.y ((upstream.coordinates input).symm.trans pointRole)
  have readX : GroupNativeSdk.readFq fq decoder (upstream.x input) =
      some (RuntimeTransferRnkLoop.base rho).x := by
    rw [GroupNativeSdk.fq_read, xValue]
  have readY : GroupNativeSdk.readFq fq decoder (upstream.y input) =
      some (RuntimeTransferRnkLoop.base rho).y := by
    rw [GroupNativeSdk.fq_read, yValue]
  have readScalar : GroupNativeSdk.readScalar fq fr decoder scalar =
      some (eval rho RuntimeTransferReduction.consumer) := by
    rw [GroupNativeSdk.scalar_read, scalarInteger, consumer]
  have nativeNonidentity : upstream.embed (upstream.promote input) ≠ 0 := by
    rw [pointEmbedding]
    exact nonidentity
  have nativeTarget :
      (⟨eval rho [(3763, (1 : Int))], eval rho [(3764, (1 : Int))]⟩ : Group.Point F) =
        model.coordinates (upstream.embed (upstream.multiply (upstream.promote input) scalar)) := by
    rw [upstream.multiplyEmbedding, scalarInteger, pointEmbedding]
    exact target
  exact ⟨q, r, input, scalar, qBound, positive, rBound, noWrap, hash,
    scalarInteger, nativeNonidentity, readX, readY, readScalar, nativeTarget⟩

set_option pp.all true in
#check @actual_native_witness
#print axioms actual_native_witness

end ShielddSecurity.RnkNativeWitness
