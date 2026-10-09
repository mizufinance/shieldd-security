import ShielddSecurity.TransferEpkNativeGenerator
import ShielddSecurity.ShielddScalarWriter
import ShielddSecurity.NativeEphemeralAdmission

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferEpkNativePreparation

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]

/-- Captured scope order: two recovery randomizers, then sender core/ext
and output core/ext. The six input-role bindings remain an independent source
obligation when this component is incorporated into the whole constructor. -/
def inputs (recovery : Fin 2 → F) (ephemeral : Fin 4 → F) : List F :=
  [recovery 0,recovery 1,ephemeral 0,ephemeral 1,ephemeral 2,ephemeral 3]

private theorem decoded_valid (codec : TransferReduction.CanonicalField F) (value : F)
    (valid : NativeEphemeralAdmission.validScalar codec value) :
    0 < codec.decode value ∧ codec.decode value < Scalar.order := by
  have nonzero : codec.decode value ≠ 0 := by
    intro zero
    apply valid.1
    have same := codec.roundtrip value
    rw [zero,Nat.cast_zero] at same
    exact same.symm
  exact ⟨Nat.pos_of_ne_zero nonzero,valid.2⟩

/-- Successful independent native witness preparation supplies all six
legality guards. The proof does not assume positive scalars, row truth or an
EPK result separately. The preparation's pure payload callbacks are explicit. -/
theorem prepared_inputs_valid {Recovery0 Recovery1 Ownership Payload : Type}
    (codec : TransferReduction.CanonicalField F) (recovery : Fin 2 → F)
    (recoveryBuild0 : F → Recovery0) (recoveryBuild1 : F → Recovery1)
    (recovered0 : Recovery0) (recovered1 : Recovery1)
    (accepted0 : NativeEphemeralAdmission.recoveryNative codec (recovery 0) recoveryBuild0 = .ok recovered0)
    (accepted1 : NativeEphemeralAdmission.recoveryNative codec (recovery 1) recoveryBuild1 = .ok recovered1)
    (ownership : Fin 2 → F)
    (ephemeral : Fin 4 → F) (checking : Group.Point F)
    (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (payload : Payload)
    (accepted : NativeEphemeralAdmission.encryptionNative codec ephemeral ownership checking
      ownershipBuild build = .ok payload) :
    ∀ value ∈ inputs recovery ephemeral,
      0 < codec.decode value ∧ codec.decode value < Scalar.order := by
  have guards := NativeEphemeralAdmission.encryption_success codec ephemeral ownership checking
    ownershipBuild build payload accepted
  have recovery0 := NativeEphemeralAdmission.recovery_success codec (recovery 0) recoveryBuild0 recovered0 accepted0
  have recovery1 := NativeEphemeralAdmission.recovery_success codec (recovery 1) recoveryBuild1 recovered1 accepted1
  intro value member
  simp only [inputs,List.mem_cons,List.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact decoded_valid codec _ recovery0
  · exact decoded_valid codec _ recovery1
  · exact decoded_valid codec _ (guards.1 0)
  · exact decoded_valid codec _ (guards.1 1)
  · exact decoded_valid codec _ (guards.1 2)
  · exact decoded_valid codec _ (guards.1 3)

def construct (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (recovery : Fin 2 → F) (ephemeral : Fin 4 → F) : Nat → F :=
  TransferEpkAllScopes.construct rho (codec.decode (recovery 0)) (codec.decode (recovery 1))
    (codec.decode (ephemeral 0)) (codec.decode (ephemeral 1))
    (codec.decode (ephemeral 2)) (codec.decode (ephemeral 3))

/-- A surrounding block whose actual linear supports avoid each of the six
owned write trees survives the complete sequential constructor. Certificates
for concrete surrounding blocks must still discharge these support tests. -/
theorem outside_rows (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (recovery : Fin 2 → F) (ephemeral : Fin 4 → F) (rows : List Row)
    (outside0 : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup RuntimeTransferEpk0ConstructiveWriteTree.tree term.1 = none)
    (outside1 : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup RuntimeTransferEpk1ConstructiveWriteTree.tree term.1 = none)
    (outside2 : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup RuntimeTransferEpk2ConstructiveWriteTree.tree term.1 = none)
    (outside3 : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup RuntimeTransferEpk3ConstructiveWriteTree.tree term.1 = none)
    (outside4 : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup RuntimeTransferEpk4ConstructiveWriteTree.tree term.1 = none)
    (outside5 : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup RuntimeTransferEpk5ConstructiveWriteTree.tree term.1 = none)
    (satisfied : Satisfies rho rows) : Satisfies (construct codec rho recovery ephemeral) rows := by
  let r1 := TransferEpkScope0PatchedCompletion.construct rho (codec.decode (recovery 0))
  let r2 := TransferEpkScope1PatchedCompletion.construct r1 (codec.decode (recovery 1))
  let r3 := TransferEpkScope2PatchedCompletion.construct r2 (codec.decode (ephemeral 0))
  let r4 := TransferEpkScope3PatchedCompletion.construct r3 (codec.decode (ephemeral 1))
  let r5 := TransferEpkScope4PatchedCompletion.construct r4 (codec.decode (ephemeral 2))
  let r6 := TransferEpkScope5PatchedCompletion.construct r5 (codec.decode (ephemeral 3))
  have sat1 := TransferEpkScope0PatchedCompletion.prior_rows rho (codec.decode (recovery 0)) rows outside0 satisfied
  have sat2 := TransferEpkScope1PatchedCompletion.prior_rows r1 (codec.decode (recovery 1)) rows outside1 sat1
  have sat3 := TransferEpkScope2PatchedCompletion.prior_rows r2 (codec.decode (ephemeral 0)) rows outside2 sat2
  have sat4 := TransferEpkScope3PatchedCompletion.prior_rows r3 (codec.decode (ephemeral 1)) rows outside3 sat3
  have sat5 := TransferEpkScope4PatchedCompletion.prior_rows r4 (codec.decode (ephemeral 2)) rows outside4 sat4
  have sat6 := TransferEpkScope5PatchedCompletion.prior_rows r5 (codec.decode (ephemeral 3)) rows outside5 sat5
  change Satisfies r6 rows
  exact sat6

variable {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)}

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
  (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream)

include upstream standard

/-- Arbitrary satisfying assignments identify all six points with native
multiplication of their actual scalar input columns. The encoder is built
from the owned raw wrapper and primitive contracts instead of a BEWrite
assumption for the whole writer. No honest-assignment premise is used. -/
theorem satisfying_native_inputs {Encoded ReadEncoded Raw : Type}
    (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddScalarWriter.Primitives Encoded Raw codec operations)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (satisfied : Satisfies rho TransferEpkAllScopes.rows) :
    TransferEpkAllScopes.nativePoints rho = (TransferEpkAllScopes.inputValues rho).map
      (NativeTransferAdmission.nativeMultiply codec (ShielddScalarWriter.writer codec operations read primitives)
        ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
        NativeSpendAuthGenerator.literal) := by
  obtain ⟨values,_count,_bounds,inputValues,points⟩ := TransferEpkNativeGenerator.sound
    upstream standard codec (ShielddScalarWriter.writer codec operations read primitives)
    rho one four imaginary nonSquare imaginarySquare satisfied
  rw [points,← inputValues,List.map_map]

/-- The six actual native input roles and a successful independent
preparation construct the six EPK scopes. Role equalities initialize input
columns; they are not desired point equations. Preservation is the existing
sequential finite write theorem, with no full-matrix preservation inferred. -/
theorem prepared_complete {Recovery0 Recovery1 Ownership Payload Encoded ReadEncoded Raw : Type}
    (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddScalarWriter.Primitives Encoded Raw codec operations)
    (rho : Nat → F) (recovery : Fin 2 → F)
    (recoveryBuild0 : F → Recovery0) (recoveryBuild1 : F → Recovery1)
    (recovered0 : Recovery0) (recovered1 : Recovery1)
    (accepted0 : NativeEphemeralAdmission.recoveryNative codec (recovery 0) recoveryBuild0 = .ok recovered0)
    (accepted1 : NativeEphemeralAdmission.recoveryNative codec (recovery 1) recoveryBuild1 = .ok recovered1)
    (ownership : Fin 2 → F) (ephemeral : Fin 4 → F)
    (checking : Group.Point F) (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (payload : Payload)
    (accepted : NativeEphemeralAdmission.encryptionNative codec ephemeral ownership checking
      ownershipBuild build = .ok payload)
    (role0 : rho 4930 = recovery 0) (role1 : rho 6334 = recovery 1)
    (role2 : rho 11611 = ephemeral 0) (role3 : rho 13629 = ephemeral 1)
    (role4 : rho 14891 = ephemeral 2) (role5 : rho 16153 = ephemeral 3)
    (one : rho 0 = 1) (linked : rho 200692 = rho 0) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1) :
    Satisfies (construct codec rho recovery ephemeral) TransferEpkAllScopes.rows ∧
      (∀ column ∈ TransferEpkAllScopes.inputColumns,
        construct codec rho recovery ephemeral column = rho column) ∧
      TransferEpkAllScopes.nativePoints (construct codec rho recovery ephemeral) =
        (inputs recovery ephemeral).map (NativeTransferAdmission.nativeMultiply codec
          (ShielddScalarWriter.writer codec operations read primitives)
          ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
          NativeSpendAuthGenerator.literal) := by
  have guards := NativeEphemeralAdmission.encryption_success codec ephemeral ownership checking
    ownershipBuild build payload accepted
  have recovery0 := NativeEphemeralAdmission.recovery_success codec (recovery 0) recoveryBuild0 recovered0 accepted0
  have recovery1 := NativeEphemeralAdmission.recovery_success codec (recovery 1) recoveryBuild1 recovered1 accepted1
  have legal0 := decoded_valid codec _ recovery0
  have legal1 := decoded_valid codec _ recovery1
  have legal2 := decoded_valid codec _ (guards.1 0)
  have legal3 := decoded_valid codec _ (guards.1 1)
  have legal4 := decoded_valid codec _ (guards.1 2)
  have legal5 := decoded_valid codec _ (guards.1 3)
  have done := TransferEpkNativeGenerator.complete upstream standard codec
    (ShielddScalarWriter.writer codec operations read primitives) rho
    (codec.decode (recovery 0)) (codec.decode (recovery 1)) (codec.decode (ephemeral 0))
    (codec.decode (ephemeral 1)) (codec.decode (ephemeral 2)) (codec.decode (ephemeral 3))
    legal0.1 legal0.2 (role0.trans (codec.roundtrip _).symm)
    legal1.1 legal1.2 (role1.trans (codec.roundtrip _).symm)
    legal2.1 legal2.2 (role2.trans (codec.roundtrip _).symm)
    legal3.1 legal3.2 (role3.trans (codec.roundtrip _).symm)
    legal4.1 legal4.2 (role4.trans (codec.roundtrip _).symm)
    legal5.1 legal5.2 (role5.trans (codec.roundtrip _).symm)
    one linked four imaginary nonSquare imaginarySquare
  refine ⟨done.1,done.2.1,?_⟩
  simpa only [inputs,List.map_cons,List.map_nil,codec.roundtrip] using done.2.2

set_option pp.all true in
#check @prepared_inputs_valid
#print axioms prepared_inputs_valid
set_option pp.all true in
#check @outside_rows
#print axioms outside_rows
set_option pp.all true in
#check @satisfying_native_inputs
#print axioms satisfying_native_inputs
set_option pp.all true in
#check @prepared_complete
#print axioms prepared_complete

end ShielddSecurity.TransferEpkNativePreparation
