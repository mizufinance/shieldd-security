import ShielddSecurity.ShielddNativeSdk
import ShielddSecurity.GroupNativeSdkPreimage

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeAuthorization

open GroupByteCodec ShielddNativeSdk

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Owned fixture/native expression after the actual key, scalar and lazy
SPEND_AUTH source programs. Fallible readers are retained in the program;
neither a default generator nor a desired output point is inserted. -/
def authorization {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model)
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (verification : K) (randomizer : R) : Option (Group.Point F) :=
  match spendAuthProgram upstream with
  | some generator =>
      match key backend upstream verification, nativePoint backend upstream generator,
          scalar (fq := fq) (fr := fr) backend randomizer with
      | some actionKey, some base, some value =>
          some (GroupNativeAuthorization.nativeAuthorization d writer actionKey base value)
      | _, _, _ => none
  | none => none

theorem owned_authorization_coordinates [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (verification : K) (randomizer : R) (actionPoint : S)
    (accepted : nonidentity upstream (upstream.keyBytes verification) = some actionPoint) :
    authorization backend upstream codec writer verification randomizer =
      some (model.coordinates (upstream.embed (upstream.keyPoint verification) +
        fr.integer randomizer • upstream.embed (upstream.promote upstream.spendAuthSubgroup))) := by
  have keyRead := key_read codec backend upstream verification actionPoint accepted
  have generatorRead := native_point_read codec backend upstream upstream.spendAuthSubgroup
  have scalarRead := scalar_read (fq := fq) (fr := fr) backend randomizer
  simp only [authorization,spend_auth_program,keyRead,generatorRead,scalarRead]
  have native := GroupNativeAuthorization.native_authorization_coordinates codec writer d imaginary model
    nonSquare imaginarySquare two (upstream.embed (upstream.keyPoint verification))
    (upstream.embed (upstream.promote upstream.spendAuthSubgroup)) (fr.integer randomizer : F)
  rw [TransferReduction.decode_canonical_cast codec _
    (lt_trans (fr.bounded randomizer) (by decide : Scalar.order < Scalar.modulus))] at native
  exact congrArg some native

/-- Production plan::rk and the circuit-native fixture expression share the
same owned readers. The two compressed admissions concern external key bytes,
independently of either arithmetic result. All codec/group contracts are
global; no successful reader or coordinate equation is a premise. -/
theorem production_authorization_agrees [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (verification : K) (randomizer : R) (actionPoint randomizedPoint : S)
    (actionAdmission : nonidentity upstream (upstream.keyBytes verification) = some actionPoint)
    (randomizedAdmission : nonidentity upstream
      (upstream.keyBytes (planRk upstream verification randomizer)) = some randomizedPoint) :
    authorization backend upstream codec writer verification randomizer =
      key backend upstream (planRk upstream verification randomizer) := by
  have computed := owned_authorization_coordinates codec writer backend upstream imaginary
    nonSquare imaginarySquare two verification randomizer actionPoint actionAdmission
  have read := key_read codec backend upstream (planRk upstream verification randomizer)
    randomizedPoint randomizedAdmission
  rw [plan_randomization upstream verification randomizer] at read
  exact computed.trans read.symm

/-- The owned admitted production point supplies the local subgroup witness
constructor: native cofactor preimage, three doubles and x inverse. Actual
allocation and original-row coverage remain separate generated joins. -/
theorem production_witness_constraints [CharP F Scalar.modulus] {Encoded Native : Type}
    (codec : TransferReduction.CanonicalField F) (writer : BEWrite codec)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (upstream : Upstream E S R K Q Signing J fq fr d model)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (two : (2 : F) ≠ 0)
    (verification : K) (randomizer : R) (randomizedPoint : S)
    (accepted : nonidentity upstream
      (upstream.keyBytes (planRk upstream verification randomizer)) = some randomizedPoint) :
    let publicPoint := model.coordinates
      (upstream.embed (upstream.keyPoint (planRk upstream verification randomizer)))
    let preimage := GroupNativeCofactor.nativePreimage d codec writer publicPoint
    let twice := GroupFixedWindows.nativeAdd d preimage preimage
    let four := GroupFixedWindows.nativeAdd d twice twice
    key backend upstream (planRk upstream verification randomizer) = some publicPoint ∧
      Group.OnCurve d preimage ∧
      GroupNativeSubgroupWitness.DoubleConstraints d preimage ∧
      GroupNativeSubgroupWitness.DoubleConstraints d twice ∧
      GroupNativeSubgroupWitness.DoubleConstraints d four ∧
      GroupNativeCofactor.nativeEight d preimage = publicPoint ∧ publicPoint.x * publicPoint.x⁻¹ = 1 := by
  dsimp only
  have legal := GroupNativeSdk.admitted_key (sdk upstream)
    (planRk upstream verification randomizer) randomizedPoint accepted
  exact ⟨key_read codec backend upstream _ randomizedPoint accepted,
    GroupNativeSubgroupWitness.native_subgroup_constraints codec writer d imaginary model
      nonSquare imaginarySquare two
      (upstream.embed (upstream.keyPoint (planRk upstream verification randomizer)))
      legal.2.1 legal.2.2⟩

set_option pp.all true in
#check @owned_authorization_coordinates
#print axioms owned_authorization_coordinates
set_option pp.all true in
#check @production_authorization_agrees
#print axioms production_authorization_agrees
set_option pp.all true in
#check @production_witness_constraints
#print axioms production_witness_constraints

end ShielddSecurity.ShielddNativeAuthorization
