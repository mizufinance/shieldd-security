"""Complete native parsed-AK IVK rows and derive final same-assignment inputs.

Uses the exact accepted singleton-role validator and previously rendered local
constructors. No extra ordinary stream, desired input meaning, or row-truth
premise is introduced. Generated candidates still require finite kernel audits.
"""
from . import generate_transfer_ivk_native_inverse as native
from . import generate_transfer_ivk_reduction_join as joins


def generate(ivk_data, ivk_export, reduction_data, reduction_export,
             parameter_root, expected_relation, readonly_lcs=()):
    native.generate(ivk_data, ivk_export, reduction_data, reduction_export,
                    parameter_root, expected_relation, readonly_lcs)
    checked = native.hashes.ivk.inspect_metadata(ivk_data, parameter_root, expected_relation)
    copy = checked['metadata']['constant_copy']
    name = 'RuntimeTransferIvkKeyPrefixOwned'
    aliases = dict(N='RuntimeTransferIvkNativeInverseOwned', K='ShielddViewingKeyCoordinates',
        S='ShielddViewingKeySeed', P='RuntimeTransferIvkInversePrefixJoin',
        C='RuntimeTransferIvkHashReductionJoin', I='RuntimeTransferIvkInverseOwnedCompletion',
        D='RuntimeHashBlock_authorization_ivk_0')
    source = '''import ShielddSecurity.RuntimeTransferIvkNativeInverseOwned
import ShielddSecurity.ShielddViewingKeyCoordinates
import ShielddSecurity.ShielddNativeIvkSdkProgram
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += '''private theorem input_frame : ∀ terms ∈ D.callInputs, ∀ term ∈ terms,
    term.1 ∉ I.ownedWrites := by
  have checked : D.callInputs.all (fun terms => terms.all
    (fun term => decide (term.1 ∉ I.ownedWrites))) = true := by decide
  intro terms member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked terms member) term present)
private theorem actual_inputs : D.callInputs = S.hashInputs := by decide
private theorem singleton_coordinates {F : Type} [Field F] (rho tau : Nat → F)
    (preserved : S.hashInputs.map (eval rho) = S.hashInputs.map (eval tau)) :
    rho 1980 = tau 1980 ∧ rho 1981 = tau 1981 := by
  have x := congrArg (fun values : List F => values[1]?.getD 0) preserved
  have y := congrArg (fun values : List F => values[2]?.getD 0) preserved
  exact ⟨by simpa [S.hashInputs,eval] using x,
    by simpa [S.hashInputs,eval] using y⟩

variable {F : Type} [Field F] {E A R Key Q Signing J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (d : F) (model : Group.StandardCurveModel J d)
variable (upstream : ShielddNativeSdk.Upstream E A R Key Q Signing J fq fr d model)
variable {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (codec : TransferReduction.CanonicalField F) (nk : Q) (point : A) (base : Nat → F)

def completeAssignment : Nat → F := N.completeAssignment fq backend codec nk
  (upstream.affine (upstream.promote point)).1 (upstream.affine (upstream.promote point)).2 base

theorem inputs_preserved :
    D.callInputs.map (eval (completeAssignment fq fr d model upstream backend codec nk point base)) =
      D.callInputs.map (eval (K.seed fq fr d model upstream backend nk point base)) := by
  have inverseKept : D.callInputs.map
      (eval (P.completed codec (K.seed fq fr d model upstream backend nk point base))) =
      D.callInputs.map (eval (C.completed codec (K.seed fq fr d model upstream backend nk point base))) := by
    apply List.map_congr_left
    intro terms member
    apply eval_agrees
    intro term present
    exact I.preserves _ term.1 (input_frame terms member term present)
  exact inverseKept.trans (C.inputs_preserved codec (K.seed fq fr d model upstream backend nk point base))

theorem key_coordinates (key : Key)
    (parsed : upstream.decodePoint (upstream.keyBytes key) = some point) :
    (⟨completeAssignment fq fr d model upstream backend codec nk point base 1980,
      completeAssignment fq fr d model upstream backend codec nk point base 1981⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.keyPoint key)) := by
  have inputs := inputs_preserved fq fr d model upstream backend codec nk point base
  rw [actual_inputs] at inputs
  have coordinates := singleton_coordinates _ _ inputs
  exact (congrArg₂ Group.Point.mk coordinates.1 coordinates.2).trans
    (K.seeded_key_coordinates fq fr d model upstream backend nk key point base parsed)
'''
    source += f'''theorem original_rows_complete [CharP F Scalar.modulus]
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr) (scalar : R)
    (one : base 0 = 1) (four : (4 : F) ≠ 0) (linked : base {copy} = base 0)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec (Poseidon.castParameters D.parameters) nk
        (upstream.affine (upstream.promote point)).1 (upstream.affine (upstream.promote point)).2) = some scalar) :
    Satisfies (completeAssignment fq fr d model upstream backend codec nk point base) P.originalRows := by
  let x := (upstream.affine (upstream.promote point)).1
  let y := (upstream.affine (upstream.promote point)).2
  have legal := ShielddViewingKeyAdmission.accepted_field_legal codec primitives _ scalar accepted
  have value := ShielddNativeIvkSdkProgram.ivk_value fq arithmetic initial square codec
    (Poseidon.castParameters D.parameters) nk x y
  change codec.decode (ShielddNativeIvkHash.fqValue (F := F) fq
    (ShielddNativeIvkSdkProgram.ivk fq arithmetic initial square codec
      (Poseidon.castParameters D.parameters) nk x y)) % Scalar.order ≠ 0 at legal
  rw [value] at legal
  have seedOne : S.seed fq backend nk x y base 0 = 1 :=
    (S.seed_preserves fq backend nk x y base 0 (by decide)).trans one
  have seedLink : S.seed fq backend nk x y base {copy} = S.seed fq backend nk x y base 0 := by
    rw [S.seed_preserves fq backend nk x y base {copy} (by decide),
      S.seed_preserves fq backend nk x y base 0 (by decide),linked]
  apply P.original_complete codec (S.seed fq backend nk x y base) seedOne four seedLink
  rw [actual_inputs,S.seed_inputs]
  exact legal
#print axioms inputs_preserved
#print axioms key_coordinates
#print axioms original_rows_complete
'''
    return name, joins._qualify(source + f'end ShielddSecurity.{name}\n', aliases)
