import ShielddSecurity.TransferAuthorizationBranchCompletion
import ShielddSecurity.TransferReduction
import ShielddSecurity.GroupWindows

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferSemanticSubgroup48

/-! Handwritten SOURCE proposal, UNRUN. Define semantic subgroup membership
using the full coordinate model and its r-annihilated points. This makes both
representation directions available without assuming the desired validity of
a selected point. It does not instantiate deployed Crypto operations, native
admission, the concrete codec, group order, or full circuit row inclusion.
Updating the abstract predicate selects an explicit mathematical interpretation;
it is not evidence that an existing native interpretation satisfies it. -/

variable {F J : Type} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]

def encodePoint (codec : TransferReduction.CanonicalField F)
    (point : Group.Point F) : TransferCore.Affine :=
  ⟨codec.decode point.x, codec.decode point.y⟩

def castPoint (point : TransferCore.Affine) : Group.Point F :=
  ⟨(point.x : F), (point.y : F)⟩

theorem encode_canonical (codec : TransferReduction.CanonicalField F)
    (point : Group.Point F) : TransferCore.CanonicalAffine (encodePoint codec point) :=
  ⟨codec.bounded _, codec.bounded _⟩

theorem cast_encode (codec : TransferReduction.CanonicalField F)
    (point : Group.Point F) : castPoint (encodePoint codec point) = point := by
  cases point with
  | mk x y =>
      change (⟨(codec.decode x : F), (codec.decode y : F)⟩ : Group.Point F) = ⟨x, y⟩
      rw [codec.roundtrip, codec.roundtrip]

def representedSubgroup (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (point : TransferCore.Affine) : Prop :=
  ∃ represented : J,
    encodePoint codec (model.coordinates represented) = point ∧
      Scalar.order • represented = 0

def withStandardSubgroup (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (crypto : TransferSem.Crypto) :
    TransferSem.Crypto :=
  {crypto with subgroup := representedSubgroup codec model}

theorem represented_canonical (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (point : TransferCore.Affine)
    (member : representedSubgroup codec model point) : TransferCore.CanonicalAffine point := by
  obtain ⟨represented, coordinates, _⟩ := member
  rw [← coordinates]
  exact encode_canonical codec _

theorem valid_iff_represented (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (crypto : TransferSem.Crypto)
    (point : TransferCore.Affine) :
    TransferSem.ValidPoint (withStandardSubgroup codec model crypto) point ↔
      ∃ represented : J,
        encodePoint codec (model.coordinates represented) = point ∧
          Scalar.order • represented = 0 := by
  constructor
  · intro valid
    exact valid.2
  · intro member
    exact ⟨represented_canonical codec model point member, member⟩

theorem represented_curve (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (point : TransferCore.Affine)
    (member : representedSubgroup codec model point) :
    Group.OnCurve d (castPoint (F := F) point) := by
  obtain ⟨represented, coordinates, _⟩ := member
  rw [← coordinates, cast_encode]
  exact model.onCurve _

theorem canonical_crypto_unchanged (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (crypto : TransferSem.Crypto) :
    TransferSem.CanonicalCrypto (withStandardSubgroup codec model crypto) ↔
      TransferSem.CanonicalCrypto crypto := Iff.rfl

/-- These are operation correspondence premises on represented group inputs.
They are not desired subgroup conclusions. The named base's subgroup order
remains an independently owned obligation; no full-group order is used here.
The universal multiplication rule concerns a mathematical total extension.
Actual native admission/correspondence must separately restrict legal scalars. -/
theorem group_closure_from_operations (codec : TransferReduction.CanonicalField F)
    {d : F} (model : Group.StandardCurveModel J d) (crypto : TransferSem.Crypto)
    (base : J) (baseOrder : Scalar.order • base = 0)
    (generator : crypto.generator = encodePoint codec (model.coordinates base))
    (multiply : ∀ n : Nat, ∀ represented : J,
      crypto.mul n (encodePoint codec (model.coordinates represented)) =
        encodePoint codec (model.coordinates (n • represented)))
    (addition : ∀ left right : J,
      crypto.add (encodePoint codec (model.coordinates left))
        (encodePoint codec (model.coordinates right)) =
          encodePoint codec (model.coordinates (left + right))) :
    TransferAuthorizationBranchCompletion.GroupClosure
      (withStandardSubgroup codec model crypto) := by
  refine ⟨⟨base, generator.symm, baseOrder⟩, ?_, ?_⟩
  · intro n point member
    obtain ⟨represented, coordinates, killed⟩ := member
    refine ⟨n • represented, ?_, ?_⟩
    · change encodePoint codec (model.coordinates (n • represented)) = crypto.mul n point
      rw [← coordinates, multiply]
    · rw [← mul_nsmul, Nat.mul_comm Scalar.order n, mul_nsmul, killed, nsmul_zero]
  · intro left right leftMember rightMember
    obtain ⟨leftGroup, leftCoordinates, leftKilled⟩ := leftMember
    obtain ⟨rightGroup, rightCoordinates, rightKilled⟩ := rightMember
    refine ⟨leftGroup + rightGroup, ?_, ?_⟩
    · change encodePoint codec (model.coordinates (leftGroup + rightGroup)) = crypto.add left right
      rw [← leftCoordinates, ← rightCoordinates, addition]
    · rw [nsmul_add, leftKilled, rightKilled, add_zero]

set_option pp.all true in
#check @encodePoint
#print axioms encodePoint
set_option pp.all true in
#check @castPoint
#print axioms castPoint
set_option pp.all true in
#check @encode_canonical
#print axioms encode_canonical
set_option pp.all true in
#check @cast_encode
#print axioms cast_encode
set_option pp.all true in
#check @representedSubgroup
#print axioms representedSubgroup
set_option pp.all true in
#check @withStandardSubgroup
#print axioms withStandardSubgroup
set_option pp.all true in
#check @represented_canonical
#print axioms represented_canonical
set_option pp.all true in
#check @valid_iff_represented
#print axioms valid_iff_represented
set_option pp.all true in
#check @represented_curve
#print axioms represented_curve
set_option pp.all true in
#check @canonical_crypto_unchanged
#print axioms canonical_crypto_unchanged
set_option pp.all true in
#check @group_closure_from_operations
#print axioms group_closure_from_operations

end ShielddSecurity.TransferSemanticSubgroup48
