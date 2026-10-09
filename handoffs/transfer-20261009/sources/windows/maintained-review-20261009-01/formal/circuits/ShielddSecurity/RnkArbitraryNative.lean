import ShielddSecurity.RuntimeTransferRnkLoop
import ShielddSecurity.RuntimeTransferRnkIvk
import ShielddSecurity.GroupNativeSdk

set_option maxHeartbeats 400000

namespace ShielddSecurity.RnkArbitraryNative

variable {F : Type} [Field F] [CharP F RuntimeTransferRnkLoop.modulus]
variable {E S R K Q J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (decoder : GroupByteCodec.BERead (F := F))
variable (model : Group.StandardCurveModel J (RuntimeTransferRnkLoop.coefficientD : F))
variable (upstream : GroupNativeSdk.Sdk fq fr (RuntimeTransferRnkLoop.coefficientD : F) model
  (E := E) (S := S) (R := R) (K := K))

/-- The scalar reader binding is an operand/source obligation. Boolean rows,
the captured reconstruction LC, and canonical Fr bounds supply its integer
meaning for an arbitrary satisfying assignment. -/
theorem scalar_from_reader (rho : Nat → F) (scalar : R)
    (readScalar : GroupNativeSdk.readScalar fq fr decoder scalar =
      some (eval rho RuntimeTransferReduction.consumer))
    (satisfied : Satisfies rho RuntimeTransferRnkLoop.bitRows) :
    ShielddSecurity.binary (ScalarBits.decodeBits rho RuntimeTransferRnkLoop.bits) =
      fr.integer scalar := by
  have consumer : (fr.integer scalar : F) = eval rho RuntimeTransferReduction.consumer :=
    Option.some.inj ((GroupNativeSdk.scalar_read fq fr decoder scalar).symm.trans readScalar)
  exact RuntimeTransferRnkIvk.decoded_scalar rho (fr.integer scalar)
    (fr.bounded scalar) consumer satisfied

/-- Coordinate readers bind the native input to the captured base columns.
No premise mentions the DH result or multiplication output. -/
theorem base_from_readers (rho : Nat → F) (input : S)
    (readX : GroupNativeSdk.readFq fq decoder (upstream.x input) =
      some (RuntimeTransferRnkLoop.base rho).x)
    (readY : GroupNativeSdk.readFq fq decoder (upstream.y input) =
      some (RuntimeTransferRnkLoop.base rho).y) :
    RuntimeTransferRnkLoop.base rho = model.coordinates (upstream.embed (upstream.promote input)) := by
  have x : (fq.integer (upstream.x input) : F) = (RuntimeTransferRnkLoop.base rho).x :=
    Option.some.inj ((GroupNativeSdk.fq_read fq decoder (upstream.x input)).symm.trans readX)
  have y : (fq.integer (upstream.y input) : F) = (RuntimeTransferRnkLoop.base rho).y :=
    Option.some.inj ((GroupNativeSdk.fq_read fq decoder (upstream.y input)).symm.trans readY)
  rw [upstream.coordinates input]
  calc
    RuntimeTransferRnkLoop.base rho =
      ⟨(RuntimeTransferRnkLoop.base rho).x, (RuntimeTransferRnkLoop.base rho).y⟩ := by
        cases RuntimeTransferRnkLoop.base rho
        rfl
    _ = ⟨(fq.integer (upstream.x input) : F), (fq.integer (upstream.y input) : F)⟩ := by
      rw [x, y]

/-- All 126 RNK windows act on arbitrary rho. The typed SDK reader bindings
identify input operands; the existing row theorem derives the native multiply
result at the actual DH columns. The owned caller must supply these bindings. -/
theorem actual_native_multiply (rho : Nat → F) (input : S) (scalar : R)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (readX : GroupNativeSdk.readFq fq decoder (upstream.x input) =
      some (RuntimeTransferRnkLoop.base rho).x)
    (readY : GroupNativeSdk.readFq fq decoder (upstream.y input) =
      some (RuntimeTransferRnkLoop.base rho).y)
    (readScalar : GroupNativeSdk.readScalar fq fr decoder scalar =
      some (eval rho RuntimeTransferReduction.consumer))
    (satisfied : Satisfies rho RuntimeTransferRnkLoop.rawRows) :
    (⟨eval rho [(3763, (1 : Int))], eval rho [(3764, (1 : Int))]⟩ : Group.Point F) =
      model.coordinates (upstream.embed (upstream.multiply (upstream.promote input) scalar)) := by
  have bitRows : Satisfies rho RuntimeTransferRnkLoop.bitRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  have scalarValue := scalar_from_reader fq fr decoder rho scalar readScalar bitRows
  have baseRole := base_from_readers fq fr decoder model upstream rho input readX readY
  have result := RuntimeTransferRnkLoop.actual_multiplication rho one four codec model
    (upstream.embed (upstream.promote input)) baseRole satisfied
  rw [scalarValue, RuntimeTransferRnkLoop.captured_output_role rho] at result
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

end ShielddSecurity.RnkArbitraryNative
