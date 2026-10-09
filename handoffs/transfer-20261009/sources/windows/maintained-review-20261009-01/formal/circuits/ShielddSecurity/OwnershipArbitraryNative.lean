import ShielddSecurity.RuntimeTransferOwnership
import ShielddSecurity.RuntimeTransferOwnershipIvk
import ShielddSecurity.GroupNativeSdk

set_option maxHeartbeats 400000

namespace ShielddSecurity.OwnershipArbitraryNative

variable {F : Type} [Field F] [CharP F RuntimeTransferOwnership.modulus]
variable {E S R K Q J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (decoder : GroupByteCodec.BERead (F := F))
variable (model : Group.StandardCurveModel J (RuntimeTransferOwnership.coefficientD : F))
variable (upstream : GroupNativeSdk.Sdk fq fr (RuntimeTransferOwnership.coefficientD : F) model
  (E := E) (S := S) (R := R) (K := K))

/-- The actual Boolean rows and reconstruction linear expression identify the
scalar integer. The caller still supplies the native input reader binding. -/
theorem scalar_from_reader (rho : Nat → F) (scalar : R)
    (readScalar : GroupNativeSdk.readScalar fq fr decoder scalar =
      some (eval rho RuntimeTransferReduction.consumer))
    (satisfied : Satisfies rho RuntimeTransferOwnership.bitRows) :
    ShielddSecurity.binary (ScalarBits.decodeBits rho RuntimeTransferOwnership.bits) =
      fr.integer scalar := by
  have consumer : (fr.integer scalar : F) = eval rho RuntimeTransferReduction.consumer :=
    Option.some.inj ((GroupNativeSdk.scalar_read fq fr decoder scalar).symm.trans readScalar)
  exact RuntimeTransferOwnershipIvk.decoded_scalar rho (fr.integer scalar)
    (fr.bounded scalar) consumer satisfied

/-- These premises bind only the native base operands to their actual columns;
no premise assumes the multiplication result or the derived tables. -/
theorem base_from_readers (rho : Nat → F) (input : S)
    (readX : GroupNativeSdk.readFq fq decoder (upstream.x input) =
      some (RuntimeTransferOwnership.base rho).x)
    (readY : GroupNativeSdk.readFq fq decoder (upstream.y input) =
      some (RuntimeTransferOwnership.base rho).y) :
    RuntimeTransferOwnership.base rho = model.coordinates (upstream.embed (upstream.promote input)) := by
  have x : (fq.integer (upstream.x input) : F) = (RuntimeTransferOwnership.base rho).x :=
    Option.some.inj ((GroupNativeSdk.fq_read fq decoder (upstream.x input)).symm.trans readX)
  have y : (fq.integer (upstream.y input) : F) = (RuntimeTransferOwnership.base rho).y :=
    Option.some.inj ((GroupNativeSdk.fq_read fq decoder (upstream.y input)).symm.trans readY)
  rw [upstream.coordinates input]
  calc
    RuntimeTransferOwnership.base rho =
      ⟨(RuntimeTransferOwnership.base rho).x, (RuntimeTransferOwnership.base rho).y⟩ := by
        cases RuntimeTransferOwnership.base rho
        rfl
    _ = ⟨(fq.integer (upstream.x input) : F), (fq.integer (upstream.y input) : F)⟩ := by
      rw [x, y]

/-- One arbitrary assignment satisfies all 126 captured windows and Boolean
rows. Their existing trace theorem derives the native result at the ownership
target columns; the owned reader/caller must instantiate the input bindings. -/
theorem actual_native_multiply (rho : Nat → F) (input : S) (scalar : R)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (readX : GroupNativeSdk.readFq fq decoder (upstream.x input) =
      some (RuntimeTransferOwnership.base rho).x)
    (readY : GroupNativeSdk.readFq fq decoder (upstream.y input) =
      some (RuntimeTransferOwnership.base rho).y)
    (readScalar : GroupNativeSdk.readScalar fq fr decoder scalar =
      some (eval rho RuntimeTransferReduction.consumer))
    (satisfied : Satisfies rho RuntimeTransferOwnership.rawRows) :
    RuntimeTransferOwnership.target rho =
      model.coordinates (upstream.embed (upstream.multiply (upstream.promote input) scalar)) := by
  have bitRows : Satisfies rho RuntimeTransferOwnership.bitRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ (List.mem_append_left _ member))
  have scalarValue := scalar_from_reader fq fr decoder rho scalar readScalar bitRows
  have baseRole := base_from_readers fq fr decoder model upstream rho input readX readY
  have result := RuntimeTransferOwnership.actual_ownership rho one four codec model
    (upstream.embed (upstream.promote input)) baseRole satisfied
  rw [scalarValue] at result
  rw [upstream.multiplyEmbedding]
  exact result

set_option pp.all true in
#check @scalar_from_reader
#print axioms scalar_from_reader
set_option pp.all true in
#check @base_from_readers
#print axioms base_from_readers
set_option pp.all true in
#check @actual_native_multiply
#print axioms actual_native_multiply

end ShielddSecurity.OwnershipArbitraryNative
