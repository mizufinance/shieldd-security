import ShielddSecurity.GroupNativeCofactor
import ShielddSecurity.GroupNativeNonidentity

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeTransferAdmission

inductive BalanceError where
  | noncanonicalBlinding
  | identityAssetGenerator
  deriving DecidableEq

abbrev Amount := Fin (2^128)
abbrev Amounts := Amount × Amount

variable {F : Type} [Field F] [DecidableEq F]

/-- Exact affine equality used by the native identity guard. -/
def isIdentity (point : Group.Point F) : Bool :=
  decide (point.x = 0) && decide (point.y = 1)

theorem identity_checked (point : Group.Point F) :
    isIdentity point = true ↔ point = Group.identityPoint := by
  constructor
  · intro checked
    have equations := Bool.and_eq_true_iff.mp checked
    have x := of_decide_eq_true equations.1
    have y := of_decide_eq_true equations.2
    cases point
    exact congrArg₂ Group.Point.mk x y
  · intro equal
    rw [equal]
    simp only [isIdentity,Group.identityPoint,decide_true,Bool.true_and]

def nativeMultiply (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d : F) (point : Group.Point F)
    (value : F) : Group.Point F :=
  GroupNativeMultiply.nativeMultiply d point (GroupByteCodec.reader (writer.encode value))

def sumAmounts (values : Amounts) : F :=
  ((values.1.val : Nat) : F) + ((values.2.val : Nat) : F)

/-- Pinned circuits/src/balance.rs native30-53: decode/order guard, actual
asset mapping, identity guard, then the two amount multiplications and blinding.
The parameters are global native function/byte/codec interfaces. None receives
a desired circuit point or an assertion that the generated x-coordinate is nonzero. -/
def balanceNative (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d : F)
    (assetGenerator : F → Group.Point F) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) : Except BalanceError (Group.Point F) :=
  if codec.decode blinding < Scalar.order then
    let generator := assetGenerator asset
    if isIdentity generator then .error .identityAssetGenerator else
      let input := nativeMultiply codec writer d generator (sumAmounts inputs)
      let output := nativeMultiply codec writer d generator (sumAmounts outputs)
      let negative : Group.Point F := ⟨-output.x,output.y⟩
      let blinded := nativeMultiply codec writer d blindingGenerator blinding
      .ok (GroupFixedWindows.nativeAdd d (GroupFixedWindows.nativeAdd d input negative) blinded)
  else .error .noncanonicalBlinding

/-- transfer::statement164-179 propagates balance::native's error before its
64-field statement can be hashed. The other native statement fields are an
independent projection callback; their contents/ordering are separate joins. -/
def statementNative {Statement : Type} (fields : Group.Point F → Statement)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec) (d : F)
    (assetGenerator : F → Group.Point F) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) : Except BalanceError Statement :=
  match balanceNative codec writer d assetGenerator blindingGenerator asset inputs outputs blinding with
  | .error error => .error error
  | .ok balance => .ok (fields balance)

/-- catalogue::evaluate93-98 obtains digest? before invoking build_with_values.
Hash/build are global callbacks, with no assumed satisfaction or circuit output. -/
def evaluateNative {Statement Circuit : Type} (fields : Group.Point F → Statement)
    (hash : Statement → F) (build : F → Circuit)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec) (d : F)
    (assetGenerator : F → Group.Point F) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) : Except BalanceError Circuit :=
  match statementNative fields codec writer d assetGenerator blindingGenerator asset inputs outputs blinding with
  | .error error => .error error
  | .ok statement => .ok (build (hash statement))

theorem balance_success_nonidentity (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (d : F)
    (assetGenerator : F → Group.Point F) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) (value : Group.Point F)
    (accepted : balanceNative codec writer d assetGenerator blindingGenerator asset inputs outputs blinding = .ok value) :
    assetGenerator asset ≠ Group.identityPoint := by
  intro identity
  have checked := (identity_checked (assetGenerator asset)).mpr identity
  by_cases canonical : codec.decode blinding < Scalar.order
  · simp only [balanceNative,if_pos canonical,checked,if_true] at accepted
    cases accepted
  · simp only [balanceNative,if_neg canonical] at accepted
    cases accepted

theorem statement_success_nonidentity {Statement : Type} (fields : Group.Point F → Statement)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec) (d : F)
    (assetGenerator : F → Group.Point F) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) (value : Statement)
    (accepted : statementNative fields codec writer d assetGenerator blindingGenerator asset inputs outputs blinding = .ok value) :
    assetGenerator asset ≠ Group.identityPoint := by
  cases observed : balanceNative codec writer d assetGenerator blindingGenerator asset inputs outputs blinding with
  | error error => simp only [statementNative,observed] at accepted; cases accepted
  | ok balance =>
      exact balance_success_nonidentity codec writer d assetGenerator blindingGenerator
        asset inputs outputs blinding balance observed

theorem evaluation_success_nonidentity {Statement Circuit : Type}
    (fields : Group.Point F → Statement) (hash : Statement → F) (build : F → Circuit)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec) (d : F)
    (assetGenerator : F → Group.Point F) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) (value : Circuit)
    (accepted : evaluateNative fields hash build codec writer d assetGenerator blindingGenerator asset inputs outputs blinding = .ok value) :
    assetGenerator asset ≠ Group.identityPoint := by
  cases observed : statementNative fields codec writer d assetGenerator blindingGenerator asset inputs outputs blinding with
  | error error => simp only [evaluateNative,observed] at accepted; cases accepted
  | ok statement =>
      exact statement_success_nonidentity fields codec writer d assetGenerator blindingGenerator
        asset inputs outputs blinding statement observed

/-- A native map cofactor constructor and the full curve's global order
discharge subgroup/nonidentity-x legality. Native success is an independent
statement input domain. No desired actual LC or inverse equation is a premise. -/
theorem successful_cofactor_x {J : Type} [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d : F) (model : Group.StandardCurveModel J d)
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (nativeImage : F → J) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) (value : Group.Point F)
    (accepted : balanceNative codec writer d (fun asset => model.coordinates (8 • nativeImage asset))
      blindingGenerator asset inputs outputs blinding = .ok value) :
    (model.coordinates (8 • nativeImage asset)).x ≠ 0 := by
  have nonidentity := balance_success_nonidentity codec writer d
    (fun asset => model.coordinates (8 • nativeImage asset)) blindingGenerator asset inputs outputs blinding value accepted
  change model.coordinates (8 • nativeImage asset) ≠ Group.identityPoint at nonidentity
  have subgroup : Scalar.order • (8 • nativeImage asset) = 0 := by
    rw [← mul_nsmul,Nat.mul_comm]
    exact fullOrder (nativeImage asset)
  apply GroupNativeNonidentity.subgroup_nonidentity_x d model (8 • nativeImage asset) subgroup
  intro zero
  apply nonidentity
  rw [zero,model.identity]

theorem successful_cofactor_inverse {J : Type} [AddCommGroup J]
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (d : F) (model : Group.StandardCurveModel J d)
    (fullOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (nativeImage : F → J) (blindingGenerator : Group.Point F)
    (asset : F) (inputs outputs : Amounts) (blinding : F) (value : Group.Point F)
    (accepted : balanceNative codec writer d (fun asset => model.coordinates (8 • nativeImage asset))
      blindingGenerator asset inputs outputs blinding = .ok value) :
    (model.coordinates (8 • nativeImage asset)).x * ((model.coordinates (8 • nativeImage asset)).x)⁻¹ = 1 :=
  mul_inv_cancel₀ (successful_cofactor_x codec writer d model fullOrder nativeImage
    blindingGenerator asset inputs outputs blinding value accepted)

set_option pp.all true in
#check @identity_checked
#print axioms identity_checked
set_option pp.all true in
#check @balance_success_nonidentity
#print axioms balance_success_nonidentity
set_option pp.all true in
#check @statement_success_nonidentity
#print axioms statement_success_nonidentity
set_option pp.all true in
#check @evaluation_success_nonidentity
#print axioms evaluation_success_nonidentity
set_option pp.all true in
#check @successful_cofactor_x
#print axioms successful_cofactor_x
set_option pp.all true in
#check @successful_cofactor_inverse
#print axioms successful_cofactor_inverse

end ShielddSecurity.NativeTransferAdmission
