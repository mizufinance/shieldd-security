"""Actual native seed ownership with derived roots/parity/double legality.

The functional sqrt API and canonical field codec are global interfaces. Their
native implementation joins are explicit separate obligations. This generates
the exact map witness seed assignment, its bit rows, and unconditional numeric
rows; the remaining asserted-square/inverse/cofactor LC transports stay open.
"""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_asset_map_comparator_completion as comparator
from . import transfer_relation as relation


def plan(data,extracted,accepted_roles):
    recipe=completion.plan(data,extracted,accepted_roles)
    canonical=comparator.plan(data,extracted,accepted_roles)
    bits=[recipe['seeds']['bit'+str(i)] for i in range(255)]
    if bits!=list(range(bits[0],bits[0]+255)):
        raise relation.RelationError('native seed exact contiguous255 source bits')
    other={label:column for label,column in recipe['seeds'].items()
           if label!='selectedRoot' and not label.startswith('bit')}
    if len(other)!=8 or set(canonical['bits'])!=set(bits):
        raise relation.RelationError('native seed exact eight other witnesses/bit roles')
    return dict(recipe=recipe,other=other,bits=bits,root=recipe['seeds']['selectedRoot'],
                owned=sorted(recipe['seeds'].values()))


def construct_seed(data,extracted,accepted_roles,base,sqrt):
    recipe=plan(data,extracted,accepted_roles)
    complete=completion.construct(data,extracted,accepted_roles,base,sqrt)
    rho=dict(base)
    for column in recipe['owned']:rho[column]=complete['assignment'][column]
    return dict(assignment=rho,plan=recipe,native_generator=complete['native_image'],proof=False,
                scope='runtime computed native seeds only; surrounding material/assertion rows and native ABI join separate')


def generate(data,extracted,accepted_roles):
    return _from_checked(plan(data,extracted,accepted_roles))


def _from_checked(result):
    """Render the retained typed seed layout; callers must preserve its receipt."""
    from .generate_hash_round import _signature_audits
    recipe=result['recipe'];other=result['other']
    copy=recipe['checked']['metadata']['constant_copy'];start=result['bits'][0];root=result['root']
    name='RuntimeTransferAssetMapNativeSeeds';core='RuntimeTransferAssetMapFirstCubicConstruction'
    numeric='RuntimeTransferAssetMapNumericConstruction';bits='RuntimeTransferAssetMapNativeBits'
    source=f'''import ShielddSecurity.{core}
import ShielddSecurity.{numeric}
import ShielddSecurity.{bits}
import ShielddSecurity.ElligatorNativeRoots
import ShielddSecurity.RuntimeJubjub
import ShielddSecurity.GroupFixedWindows
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Computed native witnesses only. Native API implementation and final asserted
-- square/inverse/cofactor LC transport remain separate from numeric completion.
abbrev modulus := {core}.modulus
def otherWrites : List Nat := {list(other.values())}
def bitColumns : List Nat := List.range' {start} 255
def seedColumns : List Nat := otherWrites ++ [{root}] ++ bitColumns
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
def nativeChoice (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : Bool :=
  ElligatorNativeRoots.choice api ({core}.nativeFirst rho)
def nativeQr (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : F :=
  ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.qrValue api 5 ({core}.nativeFirst rho))
def rawNativeY (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : F :=
  ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.selectedValue api 5
    ({core}.nativeInput rho) ({core}.nativeFirst rho))
def nativeY (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : F := ElligatorNativeParity.normalizeRoot codec (nativeChoice api rho) (rawNativeY api rho)
def nativeSelectedX (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : F :=
  if nativeChoice api rho then {core}.nativeX rho else -{core}.nativeX rho - (RuntimeElligatorAlgebra.c1 : F)
def nativeImage (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Group.Point F := Elligator.rationalPoint
  ((RuntimeElligatorAlgebra.k : F) * nativeSelectedX api rho) ((RuntimeElligatorAlgebra.k : F) * nativeY codec api rho)
def nativeDivisor (point : Group.Point F) : F :=
  (1 + Group.delta (RuntimeJubjub.d : F) point point) * (1 - Group.delta (RuntimeJubjub.d : F) point point)
def nativePoint1 (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Group.Point F := GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
  (nativeImage codec api rho) (nativeImage codec api rho)
def nativePoint2 (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Group.Point F := GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
  (nativePoint1 codec api rho) (nativePoint1 codec api rho)
def nativePoint3 (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Group.Point F := GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
  (nativePoint2 codec api rho) (nativePoint2 codec api rho)
def nativeRationalDenominator (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) : F :=
  ((RuntimeElligatorAlgebra.k : F) * nativeSelectedX api rho + 1) *
    ((RuntimeElligatorAlgebra.k : F) * nativeY codec api rho)

theorem field_odd : ringChar F ≠ 2 := by
  rw [ringChar.eq F modulus]
  decide
theorem five_nonzero : (5 : F) ≠ 0 := by
  intro zero
  have impossible := bounded_cast_injective (F := F) (p := modulus)
    (show 5 < modulus by decide) (show 0 < modulus by decide)
    (show (5 : F) = ((0 : Nat) : F) by simpa only [Nat.cast_zero] using zero)
  exact (by decide : (5 : Nat) ≠ 0) impossible
theorem five_euler [Fintype F] (cardinality : Fintype.card F = modulus) :
    (5 : F) ^ (Fintype.card F / 2) = -1 := by
  rw [cardinality]
  simpa only [RuntimeElligatorParameters.z,Int.cast_ofNat] using (RuntimeElligatorParameters.z_euler (F := F))

theorem computed_roots [Fintype F] (cardinality : Fintype.card F = modulus)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    nativeQr api rho * nativeQr api rho =
      (if nativeChoice api rho then {core}.nativeFirst rho else 5 * {core}.nativeFirst rho) ∧
    rawNativeY api rho * rawNativeY api rho =
      (if nativeChoice api rho then {core}.nativeFirst rho else {core}.nativeTv rho * {core}.nativeFirst rho) := by
  exact ElligatorNativeRoots.computed_roots api field_odd 5 ({core}.nativeInput rho)
    ({core}.nativeFirst rho) five_nonzero (five_euler cardinality)

theorem selected_square_parity [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    nativeY codec api rho * nativeY codec api rho =
      (if nativeChoice api rho then {core}.nativeFirst rho else {core}.nativeTv rho * {core}.nativeFirst rho) ∧
    codec.decode (nativeY codec api rho) % 2 = if nativeChoice api rho then 1 else 0 :=
  ElligatorNativeParity.selected_normalization codec (nativeChoice api rho) ({core}.nativeFirst rho)
    ({core}.nativeTv rho * {core}.nativeFirst rho) (rawNativeY api rho)
    ({core}.native_first_nonzero cardinality rho) (computed_roots cardinality api rho).2

theorem selected_cubic [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    nativeY codec api rho * nativeY codec api rho = Elligator.cubic
      (RuntimeElligatorAlgebra.c1 : F) (RuntimeElligatorAlgebra.c2 : F) (nativeSelectedX api rho) := by
  have square := (selected_square_parity cardinality codec api rho).1
  by_cases option : nativeChoice api rho = true
  · simpa only [nativeSelectedX,option,if_true] using square
  · rw [nativeSelectedX,if_neg option]
    rw [Elligator.alternative_cubic _ _ _ _ ({core}.native_coordinate cardinality rho)]
    simpa only [if_neg option] using square

theorem native_image_curve [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    Group.OnCurve (RuntimeJubjub.d : F) (nativeImage codec api rho) :=
  RuntimeElligatorAlgebra.selected_root_on_curve (nativeSelectedX api rho) (nativeY codec api rho)
    (selected_cubic cardinality codec api rho)

theorem native_divisor_nonzero [Fintype F] (cardinality : Fintype.card F = modulus)
    (point : Group.Point F) (valid : Group.OnCurve (RuntimeJubjub.d : F) point) : nativeDivisor point ≠ 0 := by
  have denominators := Group.denominators_nonzero (RuntimeJubjub.d : F) (RuntimeJubjub.imaginary : F)
    (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square point point valid valid
  exact mul_ne_zero denominators.1 denominators.2

theorem native_double_curve [Fintype F] (cardinality : Fintype.card F = modulus)
    (point : Group.Point F) (valid : Group.OnCurve (RuntimeJubjub.d : F) point) :
    Group.OnCurve (RuntimeJubjub.d : F) (GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F) point point) := by
  have inverseRow : nativeDivisor point * (nativeDivisor point)⁻¹ = 1 :=
    mul_inv_cancel₀ (native_divisor_nonzero cardinality point valid)
  exact (Group.shared_inverse_double_sound (RuntimeJubjub.d : F) (RuntimeJubjub.imaginary : F)
    ((nativeDivisor point)⁻¹) (RuntimeJubjub.nonsquare cardinality) RuntimeJubjub.imaginary_square
    point (GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F) point point) valid inverseRow rfl rfl).2
'''
    exports=['field_odd','five_nonzero','five_euler','computed_roots','selected_square_parity','selected_cubic',
             'native_image_curve','native_divisor_nonzero','native_double_curve']
    for i in range(1,4):
        previous='nativeImage' if i==1 else 'nativePoint'+str(i-1)
        valid='native_image_curve' if i==1 else 'native_point'+str(i-1)+'_curve'
        source+=f'''theorem native_point{i}_curve [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    Group.OnCurve (RuntimeJubjub.d : F) (nativePoint{i} codec api rho) :=
  native_double_curve cardinality ({previous} codec api rho) ({valid} cardinality codec api rho)
theorem quotient{i}_denominator_nonzero [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    nativeDivisor ({previous} codec api rho) ≠ 0 :=
  native_divisor_nonzero cardinality ({previous} codec api rho) ({valid} cardinality codec api rho)
'''
        exports+=['native_point'+str(i)+'_curve','quotient'+str(i)+'_denominator_nonzero']
    values=dict(firstInverse=f'{core}.nativeInverse rho',choice='if nativeChoice api rho then 1 else 0',
                qrRoot='nativeQr api rho',zero='if nativeRationalDenominator codec api rho = 0 then 1 else 0',
                totalInverse='(nativeRationalDenominator codec api rho)⁻¹',
                doubleInverse0='(nativeDivisor (nativeImage codec api rho))⁻¹',
                doubleInverse1='(nativeDivisor (nativePoint1 codec api rho))⁻¹',
                doubleInverse2='(nativeDivisor (nativePoint2 codec api rho))⁻¹')
    dispatch='rho column'
    for label,column in reversed(list(other.items())):dispatch=f'if column = {column} then {values[label]} else {dispatch}'
    source+=f'''def otherValues (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (column : Nat) : F := {dispatch}
def seedOther (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Nat → F := patchAssignment rho (otherValues codec api rho) otherWrites
def seedAssignment (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Nat → F := {bits}.completeAssignment codec (seedOther codec api rho) (nativeY codec api rho)
def completeAssignment (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) : Nat → F := {numeric}.completeAssignment (seedAssignment codec api rho)

theorem preserves (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (column : Nat) (outsideOther : column ∉ otherWrites)
    (outsideRoot : column ≠ {root}) (outsideBits : column < {start} ∨ {start}+255 ≤ column) :
    seedAssignment codec api rho column = rho column := by
  unfold seedAssignment
  rw [{bits}.preserves codec _ _ column outsideRoot outsideBits]
  exact patchAssignment_preserves rho _ otherWrites column outsideOther
theorem bits_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) :
    Satisfies (seedAssignment codec api rho) {bits}.rawRows := by
  apply {bits}.complete
  rw [show seedOther codec api rho {copy} = rho {copy} from patchAssignment_preserves rho _ otherWrites {copy} (by decide),
    show seedOther codec api rho 0 = rho 0 from patchAssignment_preserves rho _ otherWrites 0 (by decide),linked]
theorem numeric_complete (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (rho : Nat → F) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment codec api rho) {numeric}.rawRows := by
  apply {numeric}.complete
  rw [preserves codec api rho {copy} (by decide) (by decide) (by decide),
    preserves codec api rho 0 (by decide) (by decide) (by decide),linked]
'''
    exports+=['preserves','bits_complete','numeric_complete']
    for label,column in other.items():
        source+=f'''theorem {label}_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    seedAssignment codec api rho {column} = {values[label]} := by
  unfold seedAssignment
  rw [{bits}.preserves codec _ _ {column} (by decide) (by decide)]
  simp [seedOther,patchAssignment,otherWrites,otherValues]
'''
        exports.append(label+'_value')
    source+=f'''theorem selectedRoot_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    seedAssignment codec api rho {root} = nativeY codec api rho := by
  unfold seedAssignment {bits}.completeAssignment
  rw [writeBits_preserves _ _ _ {root} (by
    simp only [encodeBits_length]
    decide)]
  simp only [{bits}.seedValue,patchAssignment,List.mem_singleton,if_true]
'''
    exports.append('selectedRoot_value')
    for label,column in list(other.items())+[('selectedRoot',root)]:
        value='nativeY codec api rho' if label=='selectedRoot' else values[label]
        source+=f'''theorem final_{label}_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    completeAssignment codec api rho {column} = {value} := by
  unfold completeAssignment
  rw [{numeric}.seed_values _ {column} (by decide)]
  exact {label}_value codec api rho
'''
        exports.append('final_'+label+'_value')
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
