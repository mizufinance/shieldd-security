import ShielddSecurity.TransferEpkRawNative
import ShielddSecurity.TransferEpkNativePreparation

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferEpkRawPreparation

variable {F Raw Written ReadEncoded : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {model : Group.StandardCurveModel J
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)}

def inputs (recovery : Fin 2 → ShielddNativeScalar.Wrapped Raw)
    (ephemeral : Fin 4 → ShielddNativeScalar.Wrapped Raw) : List (ShielddNativeScalar.Wrapped Raw) :=
  [recovery 0,recovery 1,ephemeral 0,ephemeral 1,ephemeral 2,ephemeral 3]

def outputs (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
    (recovery : Fin 2 → ShielddNativeScalar.Wrapped Raw)
    (ephemeral : Fin 4 → ShielddNativeScalar.Wrapped Raw) : List (Option (Group.Point F)) :=
  (inputs recovery ephemeral).map (fun scalar =>
    (TransferEpkRawNative.ephemeral operations read primitives upstream scalar).map
      (ShielddNativePoint.pointValue operations))

variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
    ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F) model)
  (standard : NativeSpendAuthGenerator.StandardSpendAuth upstream)

include upstream standard

/-- Exact two recovery/four disclosure raw arguments use the same generator
reader and scalar multiplication. Success and field values are derived, with
no desired point equation or scalar legality supplied as a premise. -/
theorem outputs_value (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (recovery : Fin 2 → ShielddNativeScalar.Wrapped Raw)
    (ephemeral : Fin 4 → ShielddNativeScalar.Wrapped Raw) :
    outputs operations read primitives upstream recovery ephemeral =
      ((inputs recovery ephemeral).map (ShielddNativeScalar.value operations)).map
        (fun value => some (NativeTransferAdmission.nativeMultiply codec
          (ShielddScalarWriter.writer codec operations read
            (TransferEpkRawNative.writerPrimitives codec operations primitives))
          ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F)
          NativeSpendAuthGenerator.literal value)) := by
  rw [outputs,List.map_map]
  apply congrArg (fun f => (inputs recovery ephemeral).map f)
  funext scalar
  exact TransferEpkRawNative.ephemeral_value codec operations read primitives upstream standard scalar

/-- Independent successful guard preparations and actual raw input-column
bindings construct all six row scopes and identify their points with the raw
operations above. Whole-caller association and surrounding matrix construction
are separate obligations; no actual row or desired EPK premise is used here. -/
theorem prepared_complete {Recovery0 Recovery1 Ownership Payload : Type}
    (codec : TransferReduction.CanonicalField F)
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (read : ShielddNativeScalar.ReadPrimitives ReadEncoded Raw operations)
    (primitives : ShielddNativeEncode.Primitives (Encoded := Written) operations)
    (rho : Nat → F) (recovery : Fin 2 → ShielddNativeScalar.Wrapped Raw)
    (recoveryBuild0 : F → Recovery0) (recoveryBuild1 : F → Recovery1)
    (recovered0 : Recovery0) (recovered1 : Recovery1)
    (accepted0 : NativeEphemeralAdmission.recoveryNative codec
      (ShielddNativeScalar.value operations (recovery 0)) recoveryBuild0 = .ok recovered0)
    (accepted1 : NativeEphemeralAdmission.recoveryNative codec
      (ShielddNativeScalar.value operations (recovery 1)) recoveryBuild1 = .ok recovered1)
    (ownership : Fin 2 → F) (ephemeral : Fin 4 → ShielddNativeScalar.Wrapped Raw)
    (checking : Group.Point F) (ownershipBuild : F → Group.Point F → Ownership)
    (build : (Fin 4 → F) → Ownership → Ownership → Payload) (payload : Payload)
    (accepted : NativeEphemeralAdmission.encryptionNative codec
      (fun i => ShielddNativeScalar.value operations (ephemeral i)) ownership checking
      ownershipBuild build = .ok payload)
    (role0 : rho 4930 = ShielddNativeScalar.value operations (recovery 0))
    (role1 : rho 6334 = ShielddNativeScalar.value operations (recovery 1))
    (role2 : rho 11611 = ShielddNativeScalar.value operations (ephemeral 0))
    (role3 : rho 13629 = ShielddNativeScalar.value operations (ephemeral 1))
    (role4 : rho 14891 = ShielddNativeScalar.value operations (ephemeral 2))
    (role5 : rho 16153 = ShielddNativeScalar.value operations (ephemeral 3))
    (one : rho 0 = 1) (linked : rho 200692 = rho 0) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare
      ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1) :
    let completed := TransferEpkNativePreparation.construct codec rho
      (fun i => ShielddNativeScalar.value operations (recovery i))
      (fun i => ShielddNativeScalar.value operations (ephemeral i))
    Satisfies completed TransferEpkAllScopes.rows ∧
      (∀ column ∈ TransferEpkAllScopes.inputColumns,completed column = rho column) ∧
      outputs operations read primitives upstream recovery ephemeral =
        (TransferEpkAllScopes.nativePoints completed).map some := by
  let primitive := TransferEpkRawNative.writerPrimitives codec operations primitives
  have done := TransferEpkNativePreparation.prepared_complete upstream standard codec operations read primitive
    rho (fun i => ShielddNativeScalar.value operations (recovery i))
    recoveryBuild0 recoveryBuild1 recovered0 recovered1 accepted0 accepted1 ownership
    (fun i => ShielddNativeScalar.value operations (ephemeral i)) checking ownershipBuild build payload accepted
    role0 role1 role2 role3 role4 role5 one linked four imaginary nonSquare imaginarySquare
  refine ⟨done.1,done.2.1,?_⟩
  rw [outputs_value upstream standard codec operations read primitives,done.2.2,List.map_map]
  simp only [inputs,TransferEpkNativePreparation.inputs,List.map_cons,List.map_nil]

set_option pp.all true in
#check @outputs_value
#print axioms outputs_value
set_option pp.all true in
#check @prepared_complete
#print axioms prepared_complete

end ShielddSecurity.TransferEpkRawPreparation
