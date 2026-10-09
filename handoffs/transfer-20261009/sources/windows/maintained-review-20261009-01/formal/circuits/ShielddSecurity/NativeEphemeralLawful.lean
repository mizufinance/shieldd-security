import ShielddSecurity.NativeEphemeralAdmission
import ShielddSecurity.NativeEphemeralSdk

set_option maxHeartbeats 180000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEphemeralLawful

open GroupByteCodec

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]
variable {R : Type}

/-- The scalar is read from the same SDK Fr object used by native EPK.
Successful witness preparation supplies the independent nonzero guard.
This states neither sampler termination nor a generated point equation. -/
theorem recovery_positive {Payload : Type}
    (codec : TransferReduction.CanonicalField F) (fr : GroupNativeSdk.FrBytes R)
    (scalar : R) (build : F → Payload) (value : Payload)
    (accepted : NativeEphemeralAdmission.recoveryNative codec
      (fr.integer scalar : F) build = .ok value) :
    0 < fr.integer scalar := by
  have legal := NativeEphemeralAdmission.recovery_success codec
    (fr.integer scalar : F) build value accepted
  apply Nat.pos_of_ne_zero
  intro zero
  apply legal.1
  simp only [zero, Nat.cast_zero]

/-- All four sender/output tier scalars retain native preparation order.
Ownership preparation remains the actual independently checked native body. -/
theorem encryption_positive {Ownership Payload : Type}
    (codec : TransferReduction.CanonicalField F) (fr : GroupNativeSdk.FrBytes R)
    (scalars : Fin 4 → R) (ownership : Fin 2 → F) (checking : Group.Point F)
    (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (value : Payload)
    (accepted : NativeEphemeralAdmission.encryptionNative codec
      (fun i => (fr.integer (scalars i) : F)) ownership checking ownershipBuild build = .ok value) :
    ∀ i, 0 < fr.integer (scalars i) := by
  have legal := NativeEphemeralAdmission.encryption_success codec
    (fun i => (fr.integer (scalars i) : F)) ownership checking ownershipBuild build value accepted
  intro i
  apply Nat.pos_of_ne_zero
  intro zero
  apply (legal.1 i).1
  simp only [zero, Nat.cast_zero]

variable {E S K Q J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Derive native inverse legality and nonidentity from successful independent
recovery preparation and global SDK/curve/generator interfaces. A future row
constructor must still prove its captured coordinates are this native result. -/
theorem recovery_epk_legal {Payload : Type}
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (exactOrder : addOrderOf (sdk.embed sdk.spendAuth) = Scalar.order)
    (scalar : R) (build : F → Payload) (value : Payload)
    (accepted : NativeEphemeralAdmission.recoveryNative codec
      (fr.integer scalar : F) build = .ok value) :
    (NativeEphemeralSdk.readEphemeral codec writer decoder sdk scalar).map
      (fun point => point.x * point.x⁻¹) = some 1 ∧
      NativeEphemeralSdk.readEphemeral codec writer decoder sdk scalar ≠ some Group.identityPoint := by
  have positive := recovery_positive codec fr scalar build value accepted
  exact ⟨NativeEphemeralSdk.native_epk_inverse codec writer decoder sdk imaginary
    nonSquare imaginarySquare two exactOrder scalar positive,
    NativeEphemeralSdk.native_epk_nonidentity codec writer decoder sdk imaginary
      nonSquare imaginarySquare two exactOrder scalar positive⟩

/-- Native encryption success supplies canonical positive scalars. Exact
prime order and the same SDK objects derive all four EPK inverse laws;
no desired EPK, inverse witness, row truth or qualifier flag is a premise. -/
theorem encryption_epk_legal {Ownership Payload : Type}
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (decoder : BERead (F := F))
    (sdk : GroupNativeSdk.Sdk (E := E) (S := S) (K := K) fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (exactOrder : addOrderOf (sdk.embed sdk.spendAuth) = Scalar.order)
    (scalars : Fin 4 → R) (ownership : Fin 2 → F) (checking : Group.Point F)
    (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (value : Payload)
    (accepted : NativeEphemeralAdmission.encryptionNative codec
      (fun i => (fr.integer (scalars i) : F)) ownership checking ownershipBuild build = .ok value) :
    ∀ i, (NativeEphemeralSdk.readEphemeral codec writer decoder sdk (scalars i)).map
      (fun point => point.x * point.x⁻¹) = some 1 ∧
      NativeEphemeralSdk.readEphemeral codec writer decoder sdk (scalars i) ≠ some Group.identityPoint := by
  have positive := encryption_positive codec fr scalars ownership checking ownershipBuild build value accepted
  intro i
  exact ⟨NativeEphemeralSdk.native_epk_inverse codec writer decoder sdk imaginary
    nonSquare imaginarySquare two exactOrder (scalars i) (positive i),
    NativeEphemeralSdk.native_epk_nonidentity codec writer decoder sdk imaginary
      nonSquare imaginarySquare two exactOrder (scalars i) (positive i)⟩

set_option pp.all true in
#check @recovery_positive
#print axioms recovery_positive
set_option pp.all true in
#check @encryption_positive
#print axioms encryption_positive
set_option pp.all true in
#check @recovery_epk_legal
#print axioms recovery_epk_legal
set_option pp.all true in
#check @encryption_epk_legal
#print axioms encryption_epk_legal

end ShielddSecurity.NativeEphemeralLawful
