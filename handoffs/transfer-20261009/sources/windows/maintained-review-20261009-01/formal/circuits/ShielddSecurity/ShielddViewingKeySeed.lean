import ShielddSecurity.ShielddNativeIvkSource
import ShielddSecurity.ShielddViewingKeyAdmission
import ShielddSecurity.CompilerOwnedSeed

set_option maxHeartbeats 250000

namespace ShielddSecurity.ShielddViewingKeySeed

variable {F : Type} [Field F]

/-- SDK Fq LE bytes, pari's exact reverse, and the owned AllowZero reader.
The parser is defined from the named upstream backend primitives. Its successful
field interpretation is derived, rather than supplied for one chosen NK/AK. -/
def readValue {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (input : Q) : F :=
  (GroupNativeSdk.readFq fq (ShielddScalarReader.decoder backend) input).getD 0

theorem read_value {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (input : Q) :
    readValue fq backend input = ShielddNativeIvkHash.fqValue (F := F) fq input := by
  simp only [readValue,GroupNativeSdk.fq_read,Option.getD_some,ShielddNativeIvkHash.fqValue]

/-- Singleton roles are the independently accepted actual IVK handles.
The randomizer3766 and all other caller inputs are retained from the already
owned caller seed. Full source/row membership and exact role acceptance are
separate prerequisites to applying these three particular column numbers. -/
def values {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (nk x y : Q) : Nat → F :=
  fun column => if column = 1980 then readValue fq backend x
    else if column = 1981 then readValue fq backend y
    else if column = 1993 then readValue fq backend nk else 0

def columns : List Nat := [1980,1981,1993]

def seed {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (nk x y : Q) (base : Nat → F) : Nat → F :=
  patchAssignment base (values fq backend nk x y) columns

def hashInputs : List Linear := [[(1993,1)],[(1980,1)],[(1981,1)]]

theorem seed_inputs {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (nk x y : Q) (base : Nat → F) :
    hashInputs.map (eval (seed fq backend nk x y base)) =
      [ShielddNativeIvkHash.fqValue (F := F) fq nk,ShielddNativeIvkHash.fqValue (F := F) fq x,
        ShielddNativeIvkHash.fqValue (F := F) fq y] := by
  simp [hashInputs,seed,columns,values,patchAssignment,eval,read_value]

theorem seed_preserves {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (nk x y : Q) (base : Nat → F)
    (column : Nat) (outside : column ∉ columns) : seed fq backend nk x y base column = base column :=
  patchAssignment_preserves base _ columns column outside

theorem seed_idempotent {Q Encoded Native : Type} (fq : GroupNativeSdk.FqBytes Q)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native) (nk x y : Q) (base : Nat → F) :
    seed fq backend nk x y (seed fq backend nk x y base) = seed fq backend nk x y base :=
  CompilerOwnedSeed.patch_idempotent base (values fq backend nk x y) columns

/-- Validity is the successful result of the defined SDK reduced-scalar
nonzero guard. All hash operands are obtained from the native input readers
and seeded explicitly. No desired witness-column meaning, field-bound or
inverse-denominator premise is used. Source refinement still needs the exact
SDK affine AK coordinate extraction and loaded parameter instance. -/
theorem seeded_hash_legal [CharP F Scalar.modulus] {Q R Encoded Native : Type}
    (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (primitives : ShielddViewingKeyAdmission.Primitives fq fr)
    (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
    (codec : TransferReduction.CanonicalField F) (parameters : Poseidon.Parameters F 6)
    (nk x y : Q) (scalar : R) (base : Nat → F)
    (accepted : ShielddViewingKeyAdmission.incomingScalar primitives
      (ShielddNativeIvkSource.sdkIvk fq arithmetic initial codec parameters nk x y) = some scalar) :
    codec.decode (Poseidon.hash6 parameters 16 (hashInputs.map (eval (seed fq backend nk x y base)))) %
      Scalar.order ≠ 0 := by
  have legal := ShielddViewingKeyAdmission.accepted_field_legal codec primitives _ scalar accepted
  have meaning := ShielddNativeIvkSource.sdk_ivk_value fq arithmetic initial codec parameters nk x y
  change (fq.integer (ShielddNativeIvkSource.sdkIvk fq arithmetic initial codec parameters nk x y) : F) = _ at meaning
  rw [meaning] at legal
  rw [seed_inputs]
  exact legal

set_option pp.all true in
#check @read_value
#print axioms read_value
set_option pp.all true in
#check @seed_inputs
#print axioms seed_inputs
set_option pp.all true in
#check @seed_preserves
#print axioms seed_preserves
set_option pp.all true in
#check @seed_idempotent
#print axioms seed_idempotent
set_option pp.all true in
#check @seeded_hash_legal
#print axioms seeded_hash_legal

end ShielddSecurity.ShielddViewingKeySeed
