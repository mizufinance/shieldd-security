import ShielddSecurity.OwnershipNativeWitness
import ShielddSecurity.RnkArbitraryNative

set_option maxHeartbeats 400000

namespace ShielddSecurity.OwnershipRnkNativeWitness

/-- Both captured relations act on the same assignment and reduction consumer.
The ownership rows choose one canonical native scalar; the RNK rows derive
their multiplication with that same scalar. Input reader bindings are results.
Transport from the complete compiled relation and caller association are separate. -/
theorem actual_native_pair {F : Type} [Field F]
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
    (satisfied : Satisfies rho
      (RuntimeTransferOwnershipIvk.rawRows ++ RuntimeTransferRnkIvk.rawRows)) :
    ∃ q r : Nat, ∃ sender ring : S, ∃ scalar : R,
      q ≤ 8 ∧ 0 < r ∧ r < Scalar.order ∧ q * Scalar.order + r < Scalar.modulus ∧
      ((q * Scalar.order + r : Nat) : F) =
        Poseidon.hash6 (Poseidon.castParameters RuntimeHashBlock_authorization_ivk_0.parameters) 16
          (RuntimeHashBlock_authorization_ivk_0.callInputs.map (eval rho)) ∧
      fr.integer scalar = r ∧
      upstream.embed (upstream.promote sender) ≠ 0 ∧
      upstream.embed (upstream.promote ring) ≠ 0 ∧
      GroupNativeSdk.readFq fq decoder (upstream.x sender) =
        some (RuntimeTransferOwnership.base rho).x ∧
      GroupNativeSdk.readFq fq decoder (upstream.y sender) =
        some (RuntimeTransferOwnership.base rho).y ∧
      GroupNativeSdk.readFq fq decoder (upstream.x ring) =
        some (RuntimeTransferRnkLoop.base rho).x ∧
      GroupNativeSdk.readFq fq decoder (upstream.y ring) =
        some (RuntimeTransferRnkLoop.base rho).y ∧
      GroupNativeSdk.readScalar fq fr decoder scalar =
        some (eval rho RuntimeTransferReduction.consumer) ∧
      RuntimeTransferOwnership.target rho =
        model.coordinates (upstream.embed (upstream.multiply (upstream.promote sender) scalar)) ∧
      (⟨eval rho [(3763, (1 : Int))], eval rho [(3764, (1 : Int))]⟩ : Group.Point F) =
        model.coordinates (upstream.embed (upstream.multiply (upstream.promote ring) scalar)) := by
  have ownershipSat : Satisfies rho RuntimeTransferOwnershipIvk.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have rnkSat : Satisfies rho RuntimeTransferRnkIvk.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  obtain ⟨q, r, sender, scalar, qBound, positive, rBound, noWrap, hash,
      scalarInteger, senderNonidentity, senderX, senderY, scalarReader, ownership⟩ :=
    OwnershipNativeWitness.actual_native_witness fq fr decoder model upstream
      nativeScalarCoverage nativePointCoverage standardOrder rho one four codec ownershipSat
  have baseSat : Satisfies rho RuntimeTransferRnkBase.rawRows := by
    intro row member
    exact rnkSat row (List.mem_append_left _ member)
  have loopSat : Satisfies rho RuntimeTransferRnkLoop.rawRows := by
    intro row member
    exact baseSat row (List.mem_append_left _ member)
  obtain ⟨represented, coordinates, subgroup, nonidentity, _⟩ :=
    RuntimeTransferRnkBase.actual_rnk_multiplication rho one four codec model standardOrder baseSat
  obtain ⟨ring, pointEmbedding⟩ := nativePointCoverage represented subgroup
  have pointRole : model.coordinates (upstream.embed (upstream.promote ring)) =
      RuntimeTransferRnkLoop.base rho := by
    rw [pointEmbedding]
    exact coordinates
  have xValue : (fq.integer (upstream.x ring) : F) =
      (RuntimeTransferRnkLoop.base rho).x :=
    congrArg Group.Point.x ((upstream.coordinates ring).symm.trans pointRole)
  have yValue : (fq.integer (upstream.y ring) : F) =
      (RuntimeTransferRnkLoop.base rho).y :=
    congrArg Group.Point.y ((upstream.coordinates ring).symm.trans pointRole)
  have ringX : GroupNativeSdk.readFq fq decoder (upstream.x ring) =
      some (RuntimeTransferRnkLoop.base rho).x := by
    rw [GroupNativeSdk.fq_read, xValue]
  have ringY : GroupNativeSdk.readFq fq decoder (upstream.y ring) =
      some (RuntimeTransferRnkLoop.base rho).y := by
    rw [GroupNativeSdk.fq_read, yValue]
  have ringNonidentity : upstream.embed (upstream.promote ring) ≠ 0 := by
    rw [pointEmbedding]
    exact nonidentity
  have rnk := RnkArbitraryNative.actual_native_multiply fq fr decoder model upstream
    rho ring scalar one four codec ringX ringY scalarReader loopSat
  exact ⟨q, r, sender, ring, scalar, qBound, positive, rBound, noWrap, hash,
    scalarInteger, senderNonidentity, ringNonidentity, senderX, senderY, ringX, ringY,
    scalarReader, ownership, rnk⟩

set_option pp.all true in
#check @actual_native_pair
#print axioms actual_native_pair

end ShielddSecurity.OwnershipRnkNativeWitness
