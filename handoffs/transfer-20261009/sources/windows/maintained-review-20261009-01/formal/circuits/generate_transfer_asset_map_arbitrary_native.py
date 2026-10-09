"""Arbitrary-assignment captured asset map to its computed native program."""
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(products_source):
    match=re.search(r'theorem node1166060_sound\b.*?\(satisfied : Satisfies rho rawRows\) :\s*'
        r'eval rho (\[[^\n]+\]) = eval rho (\[[^\n]+\]) \* eval rho (\[[^\n]+\]) := by',products_source,re.S)
    if match is None:
        raise relation.RelationError('exact accepted captured first-product theorem required')
    target,left,right=match.groups()
    literal=r'\[(?:\(\d+, \(-?\d+ : Int\)\)(?:, )?)+\]'
    if target!='[(189643, (1 : Int))]' or any(re.fullmatch(literal,term) is None for term in [target,left,right]):
        raise relation.RelationError('closed actual captured linear product operands required')
    name='TransferAssetMapArbitraryNative'
    imports=['RuntimeTransferAssetMapChoice','RuntimeTransferAssetMapEncoding','RuntimeTransferAssetMapRationalImage',
        'RuntimeTransferAssetMapCofactor','RuntimeTransferAssetMapNativeSource','RuntimeTransferAssetMapHashJoin',
        'RuntimeTransferActualAssetHash','ElligatorNative']
    text=''.join(f'import ShielddSecurity.{dep}\n' for dep in imports)
    text+=f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 350000
set_option maxRecDepth 4096

def blocks : List (List Row) := [RuntimeTransferAssetMapChoice.rawRows,
  RuntimeTransferAssetMapEncoding.rawRows,RuntimeTransferAssetMapRationalImage.rawRows,
  RuntimeTransferAssetMapCofactor.rawRows,RuntimeTransferActualAssetHash.rawRows]
def rows : List Row := blocks.flatten

variable {{F : Type}} [Field F] [CharP F Scalar.modulus] [DecidableEq F] [Fintype F]

private theorem block_rows (rho : Nat → F) (satisfied : Satisfies rho rows)
    (block : List Row) (inside : block ∈ blocks) : Satisfies rho block := by
  intro row member
  exact satisfied row (List.mem_flatten.mpr ⟨block,inside,member⟩)

theorem first_coordinates (cardinality : Fintype.card F = Scalar.modulus)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows) :
    eval rho RuntimeTransferAssetMapChoice.tv = RuntimeTransferAssetMapFirstCubicConstruction.nativeTv rho ∧
    eval rho RuntimeTransferAssetMapChoice.x1 = RuntimeTransferAssetMapFirstCubicConstruction.nativeX rho ∧
    eval rho RuntimeTransferAssetMapChoice.gx1 = RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho ∧
    RuntimeTransferAssetMapChoice.choice rho = RuntimeTransferAssetMapNativeSeeds.nativeChoice api rho := by
  have choiceRows := block_rows rho satisfied RuntimeTransferAssetMapChoice.rawRows (by simp [blocks])
  have productRows : Satisfies rho RuntimeTransferAssetMapProducts0.rawRows := by
    intro row member
    exact choiceRows row (RuntimeTransferAssetMapChoice.included_RuntimeTransferAssetMapProducts0 row member)
  have tvProduct := RuntimeTransferAssetMapProducts0.node1166060_sound rho one four productRows
  have scaled : eval rho {left} = 5 * RuntimeTransferAssetMapFirstCubicConstruction.nativeInput rho := by
    have checked := Compiler.canonical_equal rho {left}
      (scaleLinear 5 RuntimeTransferAssetMapFirstCubicConstruction.input) (by decide)
    simpa only [eval_scale,Int.cast_ofNat,RuntimeTransferAssetMapFirstCubicConstruction.nativeInput] using checked
  have input : eval rho {right} = RuntimeTransferAssetMapFirstCubicConstruction.nativeInput rho := by
    exact Compiler.canonical_equal rho _ RuntimeTransferAssetMapFirstCubicConstruction.input (by decide)
  have tv : eval rho RuntimeTransferAssetMapChoice.tv = RuntimeTransferAssetMapFirstCubicConstruction.nativeTv rho := by
    simpa only [RuntimeTransferAssetMapChoice.tv,scaled,input,RuntimeTransferAssetMapFirstCubicConstruction.nativeTv] using tvProduct
  have coordinate := RuntimeTransferAssetMapChoice.first_coordinate rho one four choiceRows
  rw [tv] at coordinate
  have x := ElligatorNative.first_coordinate_unique _ _ _ _
    (RuntimeTransferAssetMapFirstCubicConstruction.native_denominator_nonzero cardinality rho)
    coordinate (RuntimeTransferAssetMapFirstCubicConstruction.native_coordinate cardinality rho)
  have cubic : eval rho RuntimeTransferAssetMapChoice.gx1 =
      RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho := by
    simpa only [x,RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst] using
      RuntimeTransferAssetMapChoice.actual_cubic rho one four choiceRows
  have option : RuntimeTransferAssetMapNativeSeeds.nativeChoice api rho = true ↔
      ∃ root : F,root * root = eval rho RuntimeTransferAssetMapChoice.gx1 := by
    rw [cubic]
    change ElligatorNativeRoots.choice api _ = true ↔ _
    refine (api.complete _).trans ⟨?_,?_⟩
    · rintro ⟨root,equation⟩;exact ⟨root,equation.symm⟩
    · rintro ⟨root,equation⟩;exact ⟨root,equation.symm⟩
  exact ⟨tv,x,cubic,RuntimeTransferAssetMapChoice.native_choice cardinality rho one four choiceRows _ option⟩

theorem selected_point (cardinality : Fintype.card F = Scalar.modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows) :
    eval rho RuntimeTransferAssetMapChoice.x = RuntimeTransferAssetMapNativeSeeds.nativeSelectedX api rho ∧
    eval rho RuntimeTransferAssetMapChoice.y = RuntimeTransferAssetMapNativeSeeds.nativeY codec api rho := by
  have choiceRows := block_rows rho satisfied RuntimeTransferAssetMapChoice.rawRows (by simp [blocks])
  have encodingRows := block_rows rho satisfied RuntimeTransferAssetMapEncoding.rawRows (by simp [blocks])
  obtain ⟨tv,x,first,chosen⟩ := first_coordinates cardinality api rho one four satisfied
  have alternate : eval rho RuntimeTransferAssetMapChoice.x2 =
      -RuntimeTransferAssetMapFirstCubicConstruction.nativeX rho - (RuntimeElligatorAlgebra.c1 : F) := by
    have checked := Compiler.canonical_equal rho RuntimeTransferAssetMapChoice.x2
      (Compiler.subtract (scaleLinear (-1) RuntimeTransferAssetMapChoice.x1) [(0,RuntimeElligatorAlgebra.c1)]) (by decide)
    rw [Compiler.eval_subtract,eval_scale,x] at checked
    simpa [eval,one] using checked
  have selectedX : eval rho RuntimeTransferAssetMapChoice.x = RuntimeTransferAssetMapNativeSeeds.nativeSelectedX api rho := by
    have selected := RuntimeTransferAssetMapChoice.selected_x rho one four choiceRows
    change eval rho RuntimeTransferAssetMapChoice.x =
      if RuntimeTransferAssetMapChoice.choice rho then eval rho RuntimeTransferAssetMapChoice.x1
      else eval rho RuntimeTransferAssetMapChoice.x2 at selected
    simpa only [chosen,x,alternate,RuntimeTransferAssetMapNativeSeeds.nativeSelectedX] using selected
  have productRows : Satisfies rho RuntimeTransferAssetMapProducts0.rawRows := by
    intro row member
    exact choiceRows row (RuntimeTransferAssetMapChoice.included_RuntimeTransferAssetMapProducts0 row member)
  have alternateG : eval rho RuntimeTransferAssetMapChoice.gx2 =
      RuntimeTransferAssetMapFirstCubicConstruction.nativeTv rho * RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho := by
    have result := RuntimeTransferAssetMapProducts0.node1166070_sound rho one four productRows
    change eval rho RuntimeTransferAssetMapChoice.gx2 = eval rho RuntimeTransferAssetMapChoice.tv *
      eval rho RuntimeTransferAssetMapChoice.gx1 at result
    simpa only [tv,first] using result
  have squared := RuntimeTransferAssetMapChoice.selected_square rho one four choiceRows
  rw [chosen,first,alternateG] at squared
  have computed := ElligatorNativeRoots.computed_roots api (RuntimeTransferAssetMapNativeSeeds.field_odd (F := F))
    5 (RuntimeTransferAssetMapFirstCubicConstruction.nativeInput rho)
    (RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho)
    (RuntimeTransferAssetMapNativeSeeds.five_nonzero (F := F)) (RuntimeTransferAssetMapNativeSeeds.five_euler cardinality)
  have normalized := ElligatorNativeParity.selected_normalization codec
    (RuntimeTransferAssetMapNativeSeeds.nativeChoice api rho)
    (RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho)
    (5 * RuntimeTransferAssetMapFirstCubicConstruction.nativeInput rho *
      RuntimeTransferAssetMapFirstCubicConstruction.nativeInput rho * RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho)
    (RuntimeTransferAssetMapNativeSeeds.rawNativeY api rho)
    (RuntimeTransferAssetMapFirstCubicConstruction.native_first_nonzero cardinality rho) computed.2
  change RuntimeTransferAssetMapNativeSeeds.nativeY codec api rho * RuntimeTransferAssetMapNativeSeeds.nativeY codec api rho =
    (if RuntimeTransferAssetMapNativeSeeds.nativeChoice api rho then RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho
    else RuntimeTransferAssetMapFirstCubicConstruction.nativeTv rho * RuntimeTransferAssetMapFirstCubicConstruction.nativeFirst rho) ∧
    codec.decode (RuntimeTransferAssetMapNativeSeeds.nativeY codec api rho) % 2 =
      if RuntimeTransferAssetMapNativeSeeds.nativeChoice api rho then 1 else 0 at normalized
  have parity := RuntimeTransferAssetMapEncoding.actual_parity codec rho one four encodingRows
  change codec.decode (eval rho RuntimeTransferAssetMapChoice.y) % 2 =
    if RuntimeTransferAssetMapChoice.choice rho then 1 else 0 at parity
  rw [chosen] at parity
  exact ⟨selectedX,ElligatorNative.codec_root_unique codec _ _ (squared.trans normalized.1.symm)
    (parity.trans normalized.2.symm)⟩

theorem actual_image (cardinality : Fintype.card F = Scalar.modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows) :
    RuntimeTransferAssetMapRationalImage.actualImage rho = RuntimeTransferAssetMapNativeSeeds.nativeImage codec api rho := by
  have rationalRows := block_rows rho satisfied RuntimeTransferAssetMapRationalImage.rawRows (by simp [blocks])
  obtain ⟨x,y⟩ := selected_point cardinality codec api rho one four satisfied
  have s := Compiler.canonical_equal rho RuntimeTransferAssetMapChoice.s
    (scaleLinear RuntimeElligatorAlgebra.k RuntimeTransferAssetMapChoice.x) (by decide)
  have t := Compiler.canonical_equal rho RuntimeTransferAssetMapChoice.t
    (scaleLinear RuntimeElligatorAlgebra.k RuntimeTransferAssetMapChoice.y) (by decide)
  rw [eval_scale,x] at s
  rw [eval_scale,y] at t
  have image := RuntimeTransferAssetMapRationalImage.rational_image rho one four rationalRows
  change RuntimeTransferAssetMapRationalImage.actualImage rho =
    Elligator.rationalPoint (eval rho RuntimeTransferAssetMapChoice.s) (eval rho RuntimeTransferAssetMapChoice.t) at image
  simpa only [s,t,RuntimeTransferAssetMapNativeSeeds.nativeImage] using image

theorem actual_cofactor (cardinality : Fintype.card F = Scalar.modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows) :
    RuntimeTransferAssetMapDouble2.output rho = RuntimeTransferAssetMapNativeSeeds.nativePoint3 codec api rho := by
  have cofactorRows := block_rows rho satisfied RuntimeTransferAssetMapCofactor.rawRows (by simp [blocks])
  have valid := RuntimeTransferAssetMapImageCurve.image_on_curve rho one four
    (fun row member => cofactorRows row (RuntimeTransferAssetMapCofactor.included0 row member))
  have first := RuntimeTransferAssetMapDouble0.double_sound rho one four
    (fun row member => cofactorRows row (RuntimeTransferAssetMapCofactor.included1 row member)) valid (RuntimeJubjub.nonsquare cardinality)
  have second := RuntimeTransferAssetMapDouble1.double_sound rho one four
    (fun row member => cofactorRows row (RuntimeTransferAssetMapCofactor.included2 row member)) first.2 (RuntimeJubjub.nonsquare cardinality)
  have third := RuntimeTransferAssetMapDouble2.double_sound rho one four
    (fun row member => cofactorRows row (RuntimeTransferAssetMapCofactor.included3 row member)) second.2 (RuntimeJubjub.nonsquare cardinality)
  have firstNative := first.1.trans (GroupFixedWindows.native_add_affine (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square _ _ valid valid).symm
  have secondNative := second.1.trans (GroupFixedWindows.native_add_affine (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square _ _ first.2 first.2).symm
  have thirdNative := third.1.trans (GroupFixedWindows.native_add_affine (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square _ _ second.2 second.2).symm
  have image := actual_image cardinality codec api rho one four satisfied
  change RuntimeTransferAssetMapDouble0.input rho = RuntimeTransferAssetMapNativeSeeds.nativeImage codec api rho at image
  have firstPoint : RuntimeTransferAssetMapDouble0.output rho =
      RuntimeTransferAssetMapNativeSeeds.nativePoint1 codec api rho := by
    simpa only [RuntimeTransferAssetMapNativeSeeds.nativePoint1,← image] using firstNative
  change RuntimeTransferAssetMapDouble1.output rho = GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
    (RuntimeTransferAssetMapDouble0.output rho) (RuntimeTransferAssetMapDouble0.output rho) at secondNative
  rw [firstPoint] at secondNative
  have secondPoint : RuntimeTransferAssetMapDouble1.output rho =
      RuntimeTransferAssetMapNativeSeeds.nativePoint2 codec api rho := secondNative
  rw [secondPoint] at thirdNative
  exact thirdNative

theorem native_hash_program (cardinality : Fintype.card F = Scalar.modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rows) :
    ElligatorNativeProgram.sourceProgram codec api (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (RuntimeElligatorAlgebra.k : F) (RuntimeJubjub.d : F)
      (Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_balance0_asset0_permutation0_0.parameters) 26 [rho 6]) =
      some (RuntimeTransferAssetMapDouble2.output rho) := by
  have hashRows := block_rows rho satisfied RuntimeTransferActualAssetHash.rawRows (by simp [blocks])
  have hashed : RuntimeTransferAssetMapFirstCubicConstruction.nativeInput rho =
      Poseidon.hash3 (Poseidon.castParameters RuntimeHashBlock_balance0_asset0_permutation0_0.parameters) 26 [rho 6] := by
    have result := RuntimeTransferActualAssetHash.actual_hash_sound rho one hashRows
    rw [RuntimeTransferAssetMapFirstCubicConstruction.nativeInput,RuntimeTransferAssetMapHashJoin.output_exact]
    simpa only [RuntimeTransferAssetMapHashJoin.inputs_exact,RuntimeTransferAssetMapHashJoin.asset,
      List.map_cons,List.map_nil,eval,Int.cast_one,one_mul,add_zero] using result
  rw [← hashed,actual_cofactor cardinality codec api rho one four satisfied]
  exact RuntimeTransferAssetMapNativeSource.native_program cardinality codec api rho

#print axioms first_coordinates
#print axioms selected_point
#print axioms actual_image
#print axioms actual_cofactor
#print axioms native_hash_program
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)
