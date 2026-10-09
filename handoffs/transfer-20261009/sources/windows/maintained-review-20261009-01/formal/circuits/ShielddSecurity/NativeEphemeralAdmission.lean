import ShielddSecurity.NativeTransferAdmission

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEphemeralAdmission

inductive Error where
  | invalidScalar
  | identityKey
  | identityEphemeral
  deriving DecidableEq

variable {F : Type} [Field F] [DecidableEq F]

/-- Pinned circuits recovery/encryption/audit native guards. A successful
statement alone supplies none of these separate witness preparation guards. -/
def validScalar (codec : TransferReduction.CanonicalField F) (value : F) : Prop :=
  value ≠ 0 ∧ codec.decode value < Scalar.order

instance validScalarDecidable (codec : TransferReduction.CanonicalField F) (value : F) :
    Decidable (validScalar codec value) := by
  unfold validScalar
  infer_instance

instance ephemeralScalarsDecidable (codec : TransferReduction.CanonicalField F)
    (ephemeral : Fin 4 → F) : Decidable (∀ i, validScalar codec (ephemeral i)) :=
  Fintype.decidableForallFintype

def recoveryNative {Payload : Type} (codec : TransferReduction.CanonicalField F)
    (randomizer : F) (build : F → Payload) : Except Error Payload :=
  if validScalar codec randomizer then .ok (build randomizer) else .error .invalidScalar

def ownershipNative {Ownership : Type} (codec : TransferReduction.CanonicalField F)
    (randomness : F) (checking : Group.Point F) (build : F → Group.Point F → Ownership) :
    Except Error Ownership :=
  if validScalar codec randomness then
    if NativeTransferAdmission.isIdentity checking then .error .identityKey
    else .ok (build randomness checking)
  else .error .invalidScalar

/-- The four native disclosure scalars are checked first. Both exact audit
ownership preparations then propagate their errors before the result is built.
The pure callbacks retain the encryption body and point/source interpretation
as an independent native interface, rather than assuming desired row values. -/
def encryptionNative {Ownership Payload : Type} (codec : TransferReduction.CanonicalField F)
    (ephemeral : Fin 4 → F) (ownership : Fin 2 → F) (checking : Group.Point F)
    (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) : Except Error Payload :=
  if ∀ i, validScalar codec (ephemeral i) then
    match ownershipNative codec (ownership 0) checking ownershipBuild with
    | .error error => .error error
    | .ok sender =>
      match ownershipNative codec (ownership 1) checking ownershipBuild with
      | .error error => .error error
      | .ok receiver => .ok (build ephemeral sender receiver)
  else .error .invalidScalar

/-- SDK Rseed::derive_esk and recovery derive_opening replace scalar zero by
one. This is deterministic replacement, not a retry or a universal property
of their input hash. The scalar field and base-coordinate field are separate. -/
def zeroToOne {S : Type} [Field S] [DecidableEq S] (value : S) : S :=
  if value = 0 then 1 else value

def publicKeyNative (point : Group.Point F) : Except Error (Group.Point F) :=
  if NativeTransferAdmission.isIdentity point then .error .identityKey else .ok point

/-- SDK RecoveryCapsule::encrypt checks payload_key, derives/replaces its
scalar, checks it, constructs EPK, and runs validate before returning. This
model preserves that guard order. Scalar multiplication and capsule fields
remain pure global native callbacks, with no generated-point premise. -/
def sdkRecoveryNative {S Payload : Type} [Field S] [DecidableEq S]
    (payloadKey : Group.Point F) (rawScalar : S) (ephemeral : S → Group.Point F)
    (fields : S → Group.Point F → Payload) : Except Error Payload :=
  if NativeTransferAdmission.isIdentity payloadKey then .error .identityKey else
    let randomizer := zeroToOne rawScalar
    if randomizer = 0 then .error .invalidScalar else
      let epk := ephemeral randomizer
      if NativeTransferAdmission.isIdentity epk then .error .identityEphemeral
      else .ok (fields randomizer epk)

theorem zeroToOne_nonzero {S : Type} [Field S] [DecidableEq S] (value : S) :
    zeroToOne value ≠ 0 := by
  by_cases zero : value = 0
  · simp only [zeroToOne,if_pos zero]
    exact one_ne_zero
  · simpa only [zeroToOne,if_neg zero] using zero

theorem recovery_success {Payload : Type} (codec : TransferReduction.CanonicalField F)
    (randomizer : F) (build : F → Payload) (value : Payload)
    (accepted : recoveryNative codec randomizer build = .ok value) :
    randomizer ≠ 0 ∧ codec.decode randomizer < Scalar.order := by
  by_cases valid : validScalar codec randomizer
  · exact valid
  · simp only [recoveryNative,if_neg valid] at accepted
    cases accepted

theorem ownership_success {Ownership : Type} (codec : TransferReduction.CanonicalField F)
    (randomness : F) (checking : Group.Point F) (build : F → Group.Point F → Ownership)
    (value : Ownership) (accepted : ownershipNative codec randomness checking build = .ok value) :
    validScalar codec randomness ∧ checking ≠ Group.identityPoint := by
  by_cases valid : validScalar codec randomness
  · refine ⟨valid,?_⟩
    intro identity
    have checked := (NativeTransferAdmission.identity_checked checking).mpr identity
    simp only [ownershipNative,if_pos valid,checked,if_true] at accepted
    cases accepted
  · simp only [ownershipNative,if_neg valid] at accepted
    cases accepted

theorem encryption_success {Ownership Payload : Type} (codec : TransferReduction.CanonicalField F)
    (ephemeral : Fin 4 → F) (ownership : Fin 2 → F) (checking : Group.Point F)
    (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (value : Payload)
    (accepted : encryptionNative codec ephemeral ownership checking ownershipBuild build = .ok value) :
    (∀ i, validScalar codec (ephemeral i)) ∧ validScalar codec (ownership 0) ∧
      validScalar codec (ownership 1) ∧ checking ≠ Group.identityPoint := by
  by_cases all : ∀ i, validScalar codec (ephemeral i)
  · cases senderObserved : ownershipNative codec (ownership 0) checking ownershipBuild with
    | error error =>
        simp only [encryptionNative,if_pos all,senderObserved] at accepted
        cases accepted
    | ok sender =>
        have senderValid := ownership_success codec (ownership 0) checking ownershipBuild sender senderObserved
        cases receiverObserved : ownershipNative codec (ownership 1) checking ownershipBuild with
        | error error =>
            simp only [encryptionNative,if_pos all,senderObserved,receiverObserved] at accepted
            cases accepted
        | ok receiver =>
            have receiverValid := ownership_success codec (ownership 1) checking ownershipBuild receiver receiverObserved
            exact ⟨all,senderValid.1,receiverValid.1,senderValid.2⟩
  · simp only [encryptionNative,if_neg all] at accepted
    cases accepted

theorem publicKey_success (point value : Group.Point F)
    (accepted : publicKeyNative point = .ok value) : point ≠ Group.identityPoint := by
  intro identity
  have checked := (NativeTransferAdmission.identity_checked point).mpr identity
  simp only [publicKeyNative,checked,if_true] at accepted
  cases accepted

theorem sdkRecovery_success {S Payload : Type} [Field S] [DecidableEq S]
    (payloadKey : Group.Point F) (rawScalar : S) (ephemeral : S → Group.Point F)
    (fields : S → Group.Point F → Payload) (value : Payload)
    (accepted : sdkRecoveryNative payloadKey rawScalar ephemeral fields = .ok value) :
    payloadKey ≠ Group.identityPoint ∧ zeroToOne rawScalar ≠ 0 ∧
      ephemeral (zeroToOne rawScalar) ≠ Group.identityPoint := by
  have nonzero := zeroToOne_nonzero rawScalar
  have payload : payloadKey ≠ Group.identityPoint := by
    intro identity
    have checked := (NativeTransferAdmission.identity_checked payloadKey).mpr identity
    simp only [sdkRecoveryNative,checked,if_true] at accepted
    cases accepted
  have notPayload : NativeTransferAdmission.isIdentity payloadKey = false := by
    cases checked : NativeTransferAdmission.isIdentity payloadKey with
    | false => rfl
    | true => exact False.elim (payload ((NativeTransferAdmission.identity_checked payloadKey).mp checked))
  refine ⟨payload,nonzero,?_⟩
  intro identity
  have checked := (NativeTransferAdmission.identity_checked (ephemeral (zeroToOne rawScalar))).mpr identity
  simp only [sdkRecoveryNative,notPayload,Bool.false_eq_true,if_false,if_neg nonzero,checked,if_true] at accepted
  cases accepted

set_option pp.all true in
#check @zeroToOne_nonzero
#print axioms zeroToOne_nonzero
set_option pp.all true in
#check @recovery_success
#print axioms recovery_success
set_option pp.all true in
#check @ownership_success
#print axioms ownership_success
set_option pp.all true in
#check @encryption_success
#print axioms encryption_success
set_option pp.all true in
#check @publicKey_success
#print axioms publicKey_success
set_option pp.all true in
#check @sdkRecovery_success
#print axioms sdkRecovery_success

end ShielddSecurity.NativeEphemeralAdmission
