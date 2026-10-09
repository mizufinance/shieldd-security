import ShielddSecurity.ShielddViewingKeyCoordinates

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddPointCoordinateSeed

variable {F : Type} [Field F]
variable {E S R K Q Signing J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (d : F) (model : Group.StandardCurveModel J d)
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)

/-- Native subgroup coordinates use the owned pari Fq reverse/AllowZero
reader. The input point is obtained by the SDK's admitted address or issuer
path; its global upstream affine law supplies the standard interpretation.
Actual source handles and the seed-before-prefix order remain row ingress
obligations, independent of this functional coordinate reader. -/
def values {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (point : S)
    (xColumn yColumn : Nat) : Nat → F := fun column =>
  if column = xColumn then ShielddViewingKeySeed.readValue fq backend
    (upstream.affine (upstream.promote point)).1
  else if column = yColumn then ShielddViewingKeySeed.readValue fq backend
    (upstream.affine (upstream.promote point)).2
  else 0

def columns (xColumn yColumn : Nat) : List Nat := [xColumn,yColumn]

def seed {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (point : S)
    (xColumn yColumn : Nat) (base : Nat → F) : Nat → F :=
  patchAssignment base (values fq fr d model upstream backend point xColumn yColumn)
    (columns xColumn yColumn)

theorem seed_preserves {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (point : S)
    (xColumn yColumn : Nat) (base : Nat → F) (column : Nat)
    (outside : column ∉ columns xColumn yColumn) :
    seed fq fr d model upstream backend point xColumn yColumn base column = base column :=
  patchAssignment_preserves base _ _ column outside

theorem seed_idempotent {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (point : S)
    (xColumn yColumn : Nat) (base : Nat → F) :
    seed fq fr d model upstream backend point xColumn yColumn
      (seed fq fr d model upstream backend point xColumn yColumn base) =
      seed fq fr d model upstream backend point xColumn yColumn base :=
  CompilerOwnedSeed.patch_idempotent base _ _

theorem coordinates {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (point : S)
    (xColumn yColumn : Nat) (distinct : xColumn ≠ yColumn) (base : Nat → F) :
    (⟨seed fq fr d model upstream backend point xColumn yColumn base xColumn,
      seed fq fr d model upstream backend point xColumn yColumn base yColumn⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.promote point)) := by
  rw [upstream.affineMeaning]
  simp [seed,values,columns,patchAssignment,Ne.symm distinct,
    ShielddViewingKeySeed.read_value,ShielddNativeIvkHash.fqValue]

theorem onCurve {Encoded Native : Type}
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (point : S)
    (xColumn yColumn : Nat) (distinct : xColumn ≠ yColumn) (base : Nat → F) :
    Group.OnCurve d (⟨seed fq fr d model upstream backend point xColumn yColumn base xColumn,
      seed fq fr d model upstream backend point xColumn yColumn base yColumn⟩ : Group.Point F) := by
  rw [coordinates fq fr d model upstream backend point xColumn yColumn distinct base]
  exact model.onCurve _

set_option pp.all true in
#check @seed_preserves
#print axioms seed_preserves
set_option pp.all true in
#check @seed_idempotent
#print axioms seed_idempotent
set_option pp.all true in
#check @coordinates
#print axioms coordinates
set_option pp.all true in
#check @onCurve
#print axioms onCurve

end ShielddSecurity.ShielddPointCoordinateSeed
