import ShielddSecurity.GroupByteCodec
import ShielddSecurity.GroupFixedWindows

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupNativeAuthorization

open GroupByteCodec

variable {F : Type} [Field F]

/-- Global SDK affine-coordinate byte interface. The intended `coordinates`
is `model.coordinates ∘ embed`, with SDK SubgroupPoint embedded in the full
Jubjub group. Pinned primitives/src/lib.rs converts ExtendedPoint to affine,
then encodes u/v little endian. This interface concerns every SDK input; it
does not assume an encoding or group-operation result for an output witness.
The SDK/FFI instantiation remains an explicit source interpretation boundary. -/
structure CoordinateBytes {S : Type} (codec : TransferReduction.CanonicalField F)
    (coordinates : S → Group.Point F) where
  x : S → Bytes
  y : S → Bytes
  xLittleEndian : ∀ point index,
    (x point index).val = littleEndianByte (codec.decode (coordinates point).x) index.val
  yLittleEndian : ∀ point index,
    (y point index).val = littleEndianByte (codec.decode (coordinates point).y) index.val

/-- Exact two coordinate reads in pinned group.rs103-115. Rust calls `expect`
on each read; returning `some` here proves those calls succeed under the
independent canonical-byte contracts. No arbitrary default point is used. -/
def readPoint (decoder : BERead (F := F)) (x y : Bytes) : Option (Group.Point F) :=
  match decoder.decode (reverseBytes x), decoder.decode (reverseBytes y) with
  | some xValue, some yValue => some ⟨xValue,yValue⟩
  | _, _ => none

theorem coordinate_read (codec : TransferReduction.CanonicalField F)
    (decoder : BERead (F := F)) (value : F) (bytes : Bytes)
    (byteValues : ∀ index,
      (bytes index).val = littleEndianByte (codec.decode value) index.val) :
    decoder.decode (reverseBytes bytes) = some value := by
  have decoded := reversed_coordinate_read decoder (codec.decode value)
    (codec.bounded value) bytes byteValues
  rw [codec.roundtrip] at decoded
  exact decoded

theorem read_point_coordinates {S : Type}
    (codec : TransferReduction.CanonicalField F) (decoder : BERead (F := F))
    (coordinates : S → Group.Point F) (bytes : CoordinateBytes codec coordinates)
    (point : S) : readPoint decoder (bytes.x point) (bytes.y point) =
      some (coordinates point) := by
  have xRead := coordinate_read codec decoder (coordinates point).x
    (bytes.x point) (bytes.xLittleEndian point)
  have yRead := coordinate_read codec decoder (coordinates point).y
    (bytes.y point) (bytes.yLittleEndian point)
  cases representation : coordinates point with
  | mk x y =>
    simp only [representation] at xRead yRead ⊢
    simp only [readPoint,xRead,yRead]

/-- Pinned circuits/src/fixtures.rs379-382 constructs RK with this native
add/multiply expression; note/tests.rs24 uses the same expression. The circuit
authorization in note.rs68-76 instead uses canonical bits, fixed windows and
equality rows. Its actual same-assignment join is a separate generated proof.
This definition proves the native operation, without identifying a fixture
with the production transaction builder or a public compressed-RK decoder. -/
def nativeAuthorization (d : F) {codec : TransferReduction.CanonicalField F}
    (writer : BEWrite codec) (key spendAuth : Group.Point F) (randomizer : F) :
    Group.Point F :=
  GroupFixedWindows.nativeAdd d key
    (GroupNativeMultiply.nativeMultiply d spendAuth (reader (writer.encode randomizer)))

theorem native_authorization_coordinates [CharP F Scalar.modulus]
    {J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : BEWrite codec) (d imaginary : F) (model : Group.StandardCurveModel J d)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (key spendAuth : J) (randomizer : F) :
    nativeAuthorization d writer (model.coordinates key) (model.coordinates spendAuth) randomizer =
      model.coordinates (key + codec.decode randomizer • spendAuth) := by
  unfold nativeAuthorization
  rw [native_reader_coordinates codec writer d imaginary model nonSquare imaginarySquare
    two spendAuth randomizer]
  exact GroupFixedWindows.native_add_coordinates d imaginary model nonSquare imaginarySquare
    key (codec.decode randomizer • spendAuth)

/-- Native operation after the two actual coordinate-read pairs. The supplied
SDK generator input is intended to be pinned generators::SPEND_AUTH; that
named standard-group embedding/source identity is independent of this result. -/
def readAuthorization (decoder : BERead (F := F))
    {codec : TransferReduction.CanonicalField F} (writer : BEWrite codec) (d : F)
    (keyX keyY spendX spendY : Bytes) (randomizer : F) : Option (Group.Point F) :=
  match readPoint decoder keyX keyY, readPoint decoder spendX spendY with
  | some key, some spendAuth => some (nativeAuthorization d writer key spendAuth randomizer)
  | _, _ => none

theorem read_authorization_coordinates [CharP F Scalar.modulus]
    {S J : Type} [AddCommGroup J] (codec : TransferReduction.CanonicalField F)
    (writer : BEWrite codec) (decoder : BERead (F := F))
    (d imaginary : F) (model : Group.StandardCurveModel J d)
    (embed : S → J) (bytes : CoordinateBytes codec (fun point => model.coordinates (embed point)))
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (key spendAuth : S) (randomizer : F) :
    readAuthorization decoder writer d (bytes.x key) (bytes.y key)
      (bytes.x spendAuth) (bytes.y spendAuth) randomizer =
      some (model.coordinates (embed key + codec.decode randomizer • embed spendAuth)) := by
  have keyRead := read_point_coordinates codec decoder
    (fun point => model.coordinates (embed point)) bytes key
  have spendRead := read_point_coordinates codec decoder
    (fun point => model.coordinates (embed point)) bytes spendAuth
  simp only [readAuthorization,keyRead,spendRead]
  exact congrArg some (native_authorization_coordinates codec writer d imaginary model
    nonSquare imaginarySquare two (embed key) (embed spendAuth) randomizer)

set_option pp.all true in
#check @coordinate_read
#print axioms coordinate_read
set_option pp.all true in
#check @read_point_coordinates
#print axioms read_point_coordinates
set_option pp.all true in
#check @native_authorization_coordinates
#print axioms native_authorization_coordinates
set_option pp.all true in
#check @read_authorization_coordinates
#print axioms read_authorization_coordinates

end ShielddSecurity.GroupNativeAuthorization
