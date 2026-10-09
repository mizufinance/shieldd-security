import ShielddSecurity.ElligatorNativeRoots
import ShielddSecurity.GroupNativeCofactor

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.ElligatorNativeProgram

variable {F : Type} [Field F] [DecidableEq F]

/-- Pinned circuits map::x_coordinates, with the global coefficient values
passed separately from the independently supplied native input u. -/
def firstX (c1 u : F) : F := -c1 * (1 + 5 * u * u)⁻¹

def firstCubic (c1 c2 u : F) : F := Elligator.cubic c1 c2 (firstX c1 u)

def sourceRootOption (api : ElligatorNativeRoots.SqrtAPI F) (first alternative : F) : Option F :=
  if (api.sqrt first).isSome then api.sqrt first else api.sqrt alternative

/-- None records native fallback square-root failure. Availability must be
derived from the finite-field/nonsquare parameters, rather than postulated
for the desired map result. SDK unwrap_or(0) and circuit expect therefore
take the same successful branch after the availability proof. -/
def sourceProgram (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (c1 c2 k d u : F) : Option (Group.Point F) :=
  let x1 := firstX c1 u
  let first := firstCubic c1 c2 u
  let choice := (api.sqrt first).isSome
  let x := if choice then x1 else -x1-c1
  (sourceRootOption api first (5*u*u*first)).map fun rawRoot =>
    GroupNativeCofactor.nativeEight d (Elligator.rationalPoint (k*x)
      (k*ElligatorNativeParity.normalizeRoot codec choice rawRoot))

def generatorValue (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (c1 c2 k d u : F) : Group.Point F :=
  let x1 := firstX c1 u
  let first := firstCubic c1 c2 u
  let choice := ElligatorNativeRoots.choice api first
  let x := if choice then x1 else -x1-c1
  let root := ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.selectedValue api 5 u first)
  GroupNativeCofactor.nativeEight d (Elligator.rationalPoint (k*x)
    (k*ElligatorNativeParity.normalizeRoot codec choice root))

theorem source_root_option (api : ElligatorNativeRoots.SqrtAPI F) (first alternative : F) :
    sourceRootOption api first alternative = api.sqrt
      (if (api.sqrt first).isSome then first else alternative) := by
  cases choice : (api.sqrt first).isSome <;> simp only
    [sourceRootOption,choice,Bool.false_eq_true,if_false,if_true]

theorem source_defined [Fintype F] (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (odd : ringChar F ≠ 2)
    (fiveNonzero : (5 : F) ≠ 0) (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)
    (c1 c2 k d u : F) :
    sourceProgram codec api c1 c2 k d u = some (generatorValue codec api c1 c2 k d u) := by
  have square := ElligatorNativeRoots.selected_square api odd (5 : F) u
    (firstCubic c1 c2 u) fiveNonzero fiveEuler
  have present := (api.complete _).mpr square
  have option : sourceRootOption api (firstCubic c1 c2 u) (5*u*u*firstCubic c1 c2 u) =
      api.sqrt (ElligatorNativeRoots.selectedValue api 5 u (firstCubic c1 c2 u)) := by
    rw [source_root_option]
    rfl
  cases selected : api.sqrt (ElligatorNativeRoots.selectedValue api 5 u (firstCubic c1 c2 u)) with
  | none =>
      have impossible : (none : Option F).isSome = true := by simpa only [selected] using present
      cases impossible
  | some root =>
      simp only [sourceProgram,option,selected,Option.map_some,generatorValue,
        ElligatorNativeRoots.rootValue,ElligatorNativeRoots.choice,Option.getD_some]
      rfl

/-- Exact native encode()[31] low-bit boundary from the global BE byte
contract. Its pinned FFI instantiation is the existing independent source join. -/
theorem low_byte_parity (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (root : F) :
    (writer.encode root ⟨31,by decide⟩).val % 2 = codec.decode root % 2 := by
  rw [writer.byteValue]
  simp only [GroupScalarCodec.bigEndianByte,Nat.sub_self,Nat.mul_zero,pow_zero,Nat.div_one]
  simpa only [pow_zero,Nat.div_one] using GroupScalarCodec.low_byte_bit (codec.decode root) 0 (by decide)

def encodedNormalize (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (choice : Bool) (root : F) : F :=
  if decide ((writer.encode root ⟨31,by decide⟩).val % 2 = 1) != choice then -root else root

theorem encoded_normalize (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (choice : Bool) (root : F) :
    encodedNormalize codec writer choice root = ElligatorNativeParity.normalizeRoot codec choice root := by
  unfold encodedNormalize
  rw [low_byte_parity codec writer root]
  have parity : codec.decode root % 2 = 0 ∨ codec.decode root % 2 = 1 := by
    have bound := Nat.mod_lt (codec.decode root) (by decide : 0 < 2)
    omega
  rcases parity with even | odd
  · cases choice <;> simp [ElligatorNativeParity.normalizeRoot,even]
  · cases choice <;> simp [ElligatorNativeParity.normalizeRoot,odd]

set_option pp.all true in
#check @source_root_option
#print axioms source_root_option
set_option pp.all true in
#check @source_defined
#print axioms source_defined
set_option pp.all true in
#check @low_byte_parity
#print axioms low_byte_parity
set_option pp.all true in
#check @encoded_normalize
#print axioms encoded_normalize

end ShielddSecurity.ElligatorNativeProgram
