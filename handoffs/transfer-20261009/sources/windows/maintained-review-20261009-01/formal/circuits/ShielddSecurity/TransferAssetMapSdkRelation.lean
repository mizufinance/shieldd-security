import ShielddSecurity.TransferAssetMapArbitraryNative
import ShielddSecurity.RuntimeBalanceOwnedAssetSeedReuse
import ShielddSecurity.RuntimeBalanceVariableWindow000Point0Completion

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferAssetMapSdkRelation

variable {F E S R K Q Signing J Encoded : Type}
variable [Field F] [CharP F Scalar.modulus] [DecidableEq F] [Fintype F] [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr (RuntimeJubjub.d : F) model)
variable (codec : TransferReduction.CanonicalField F)
variable (hex : ShielddNativeParameterBytes.HexCodec Encoded)
variable (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
variable (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
variable (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
variable (api : ElligatorNativeRoots.SqrtAPI F)
variable (ops : NativeAssetMap.Primitives fq api)
variable (points : NativeAssetMap.PointPrimitives fq upstream)

include codec

/-- The owned native hash/map program determines the arbitrary circuit output.
Only its input's native field meaning is supplied; no generated assignment,
chosen root, or desired output point is a premise. -/
theorem coordinates (cardinality : Fintype.card F = Scalar.modulus)
    (rho : Nat → F) (asset : Q) (meaning : rho 6 = (fq.integer asset : F))
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho TransferAssetMapArbitraryNative.rows) :
    RuntimeTransferAssetMapDouble2.output rho = model.coordinates
      (upstream.embed (upstream.promote
        (NativeAssetGeneratorSource.valueGenerator hex fq arithmetic initial square api ops upstream points asset))) := by
  have denominator : Group.NoUnitSquare (-5 : F) := by
    have residue := Compiler.coefficient_mod (F := F) (p := Scalar.modulus) (-5)
    have checked : (-5 : Int) % (Scalar.modulus : Int) = RuntimeElligatorParameters.negative_z := by decide
    rw [checked] at residue
    have negative := RuntimeElligatorParameters.negative_z_nonsquare (F := F) cardinality
    rw [residue] at negative
    simpa only [Int.cast_neg,Int.cast_ofNat] using negative
  have nonzero : (NativeAssetMap.coefficientK : F) ≠ 0 := by
    rw [← RuntimeBalanceOwnedAssetSeedReuse.coefficient_k]
    exact RuntimeElligatorAlgebra.k_nonzero
  have edwards : (NativeAssetMap.coefficientK : F) * (RuntimeJubjub.d : F) = 40960 := by
    rw [← RuntimeBalanceOwnedAssetSeedReuse.coefficient_k]
    have result := RuntimeElligatorAlgebra.edwards (F := F)
    norm_num only [RuntimeElligatorAlgebra.j,Int.cast_ofNat] at result
    exact result
  have native := NativeAssetGeneratorSource.coordinates hex fq arithmetic initial square codec api ops upstream points
    (RuntimeJubjub.imaginary : F) (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square
    nonzero denominator edwards RuntimeTransferAssetMapNativeSeeds.field_odd
    RuntimeTransferAssetMapNativeSeeds.five_nonzero (RuntimeTransferAssetMapNativeSeeds.five_euler cardinality) asset
  rw [RuntimeBalanceOwnedAssetSeedReuse.parameter_table,
    ← RuntimeBalanceOwnedAssetSeedReuse.coefficient_c1,← RuntimeBalanceOwnedAssetSeedReuse.coefficient_c2,
    ← RuntimeBalanceOwnedAssetSeedReuse.coefficient_k,← meaning] at native
  have captured := TransferAssetMapArbitraryNative.native_hash_program cardinality codec api rho one four satisfied
  have defined := ElligatorNativeProgram.source_defined codec api RuntimeTransferAssetMapNativeSeeds.field_odd
    RuntimeTransferAssetMapNativeSeeds.five_nonzero (RuntimeTransferAssetMapNativeSeeds.five_euler cardinality)
    (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
    (Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_balance0_asset0_permutation0_0.parameters) 26 [rho 6])
  have point := Option.some.inj (defined.symm.trans captured)
  exact point.symm.trans native.symm

/-- The balance variable loop reads the identical captured map output columns. -/
theorem balance_input (cardinality : Fintype.card F = Scalar.modulus)
    (rho : Nat → F) (asset : Q) (meaning : rho 6 = (fq.integer asset : F))
    (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho TransferAssetMapArbitraryNative.rows) :
    RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho = model.coordinates
      (upstream.embed (upstream.promote
        (NativeAssetGeneratorSource.valueGenerator hex fq arithmetic initial square api ops upstream points asset))) := by
  have captured : RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho =
      RuntimeTransferAssetMapDouble2.output rho := rfl
  exact captured.trans (coordinates fq fr model upstream codec hex arithmetic initial square api ops points
    cardinality rho asset meaning one four satisfied)

set_option pp.all true in
#check @coordinates
#print axioms coordinates
set_option pp.all true in
#check @balance_input
#print axioms balance_input

end ShielddSecurity.TransferAssetMapSdkRelation
