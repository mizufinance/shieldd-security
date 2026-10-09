"""Exact original-product/shared-inverse joins for the three map doubles.

Each double has a bounded row dependency list and independent source-path
selection. The final composition proves curve/subgroup consequences from the
actual image curve join and explicit global standard-curve/order contracts.
"""
from . import transfer_asset_map as maps, transfer_relation as relation
from .transfer_balance_rows import combine


def _plan(checked, stage):
    nodes = checked['nonlinear']
    x, y = checked['points'][stage]
    output = checked['points'][stage + 1]
    xx, yy, dt, plus, minus, divisor, inverse = checked['auxiliary'][stage]
    selected = {}

    def matches(a, b, out=None):
        return [(offset, index, result) for offset, (index, left, right, result) in enumerate(nodes)
                if ((left, right) == (a, b) or (left, right) == (b, a))
                and (out is None or result == out)]

    def product(label, a, b, out=None):
        candidates = matches(a, b, out)
        if len(candidates) != 1:
            raise relation.RelationError('map cofactor exact unique source product: ' + label)
        offset, index, result = candidates[0]
        selected[label] = (offset // 16, index, a, b, result)
        return result

    product('xx', x, x, xx)
    product('yy', y, y, yy)
    base = product('delta', xx, yy, maps._scale(dt, pow(maps.D, -1, maps.P)))
    product('divisor', plus, minus, divisor)
    # The original Point.add may allocate both x*y and y*x separately.
    # Preserve the exact two output LCs; only pair order is immaterial.
    paths = set()
    cross = matches(x, y)
    if len(cross) > 8:
        raise relation.RelationError('map cofactor cross source bound')
    for a in cross:
        for b in cross:
            pair = tuple(sorted((a, b)))
            total = combine(a[2], b[2])
            for times in matches(total, minus):
                for result in matches(times[2], inverse, output[0]):
                    paths.add((pair, times, result))
    if len(paths) != 1:
        raise relation.RelationError('map cofactor exact unique double-x source path')
    pair, times, result = next(iter(paths))
    for label, record in zip(('crossLeft', 'crossRight'), pair):
        offset, index, out = record
        selected[label] = (offset // 16, index, x, y, out)
    total = combine(pair[0][2], pair[1][2])
    selected['xTimesMinus'] = (times[0] // 16, times[1], total, minus, times[2])
    selected['xOutput'] = (result[0] // 16, result[1], times[2], inverse, result[2])
    y_times = product('yTimesPlus', combine(yy, xx), plus)
    product('yOutput', y_times, inverse, output[1])
    return dict(selected=selected, delta_base=base, input=(x, y), output=output,
                xx=xx, yy=yy, dt=dt, plus=plus, minus=minus, divisor=divisor, inverse=inverse)


def generate_doubles(data, extracted, accepted_roles):
    from .generate_hash_round import linear, _signature_audits
    checked = maps.certificates(data, extracted, accepted_roles)['checked']
    modules = {}
    for stage in range(3):
        plan = _plan(checked, stage)
        selected = plan['selected']
        chunks = sorted({record[0] for record in selected.values()})
        dependencies = ['RuntimeTransferAssetMapProducts' + str(chunk) for chunk in chunks]
        dependencies.append('RuntimeTransferAssetMapInverses')
        name = 'RuntimeTransferAssetMapDouble' + str(stage)
        source = ''.join('import ShielddSecurity.' + dep + '\n' for dep in dependencies)
        source += f'''import ShielddSecurity.GroupWindows
import ShielddSecurity.RuntimeJubjub
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact map source metadata SHA256 {checked['metadata_sha256']}; native loop join separate.
def modulus : Nat := {maps.P}
def rawRows : List Row := ''' + ' ++ '.join(dep + '.rawRows' for dep in dependencies) + '\n'
        for label in ('xx', 'yy', 'dt', 'plus', 'minus', 'divisor', 'inverse'):
            source += 'def ' + label + ' : Linear := ' + linear(plan[label]) + '\n'
        for label in ('input', 'output'):
            x, y = plan[label]
            source += f'''def {label} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(x)},eval rho {linear(y)}⟩
'''
        exports = []
        for offset, dependency in enumerate(dependencies):
            export = 'included' + str(offset)
            source += f'''theorem {export} : ∀ row ∈ {dependency}.rawRows, row ∈ rawRows := by
  intro row member
  simp only [rawRows,List.mem_append]
  tauto
'''
            exports.append(export)

        def premise(dep):
            offset = dependencies.index(dep)
            return f'(fun row member => satisfied row (included{offset} row member))'

        def product(label):
            chunk, index, a, b, out = selected[label]
            dep = 'RuntimeTransferAssetMapProducts' + str(chunk)
            aliases = {plan[k]: k for k in ('xx', 'yy', 'dt', 'plus', 'minus', 'divisor', 'inverse')}
            term = lambda lc: aliases.get(lc, linear(lc))
            return f'''  have {label}Product : eval rho {linear(out)} = eval rho {linear(a)} * eval rho {linear(b)} := by
    simpa only [mul_comm] using {dep}.node{index}_sound rho one four {premise(dep)}
  change eval rho {term(out)} = eval rho {term(a)} * eval rho {term(b)} at {label}Product
'''

        common = '''{F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows)'''
        source += f'''theorem delta_value {common} :
    eval rho dt = Group.delta (RuntimeJubjub.d : F) (input rho) (input rho) := by
''' + ''.join(product(label) for label in ('xx', 'yy', 'delta'))
        source += f'''  have scaled := Compiler.canonical_equal rho dt
    (scaleLinear RuntimeJubjub.d {linear(plan['delta_base'])}) (by decide)
  rw [eval_scale,deltaProduct,xxProduct,yyProduct] at scaled
  change eval rho dt = _ at scaled
  calc
    _ = _ := scaled
    _ = _ := by unfold Group.delta input; ring

theorem plus_value {common} :
    eval rho plus = 1 + Group.delta (RuntimeJubjub.d : F) (input rho) (input rho) := by
  have actual := Compiler.canonical_equal rho plus ([(0,1)] ++ dt) (by decide)
  have unit : eval rho [(0,1)] = (1 : F) := by simp [eval,one]
  rw [eval_append,unit,delta_value rho one four satisfied] at actual
  exact actual

theorem minus_value {common} :
    eval rho minus = 1 - Group.delta (RuntimeJubjub.d : F) (input rho) (input rho) := by
  have actual := Compiler.canonical_equal rho minus (Compiler.subtract [(0,1)] dt) (by decide)
  have unit : eval rho [(0,1)] = (1 : F) := by simp [eval,one]
  rw [Compiler.eval_subtract,unit,delta_value rho one four satisfied] at actual
  exact actual

theorem inverse_row {common} :
    ((1 + Group.delta (RuntimeJubjub.d : F) (input rho) (input rho)) *
      (1 - Group.delta (RuntimeJubjub.d : F) (input rho) (input rho))) * eval rho inverse = 1 := by
''' + product('divisor')
        source += f'''  have quotient := RuntimeTransferAssetMapInverses.equation{stage+1}_sound rho one four
    {premise('RuntimeTransferAssetMapInverses')}
  change eval rho inverse * eval rho divisor = eval rho [(0,1)] at quotient
  have unit : eval rho [(0,1)] = (1 : F) := by simp [eval,one]
  rw [unit,divisorProduct,plus_value rho one four satisfied,minus_value rho one four satisfied] at quotient
  simpa only [mul_comm] using quotient

theorem x_value {common} :
    (output rho).x = Group.cross (input rho) (input rho) *
      (1 - Group.delta (RuntimeJubjub.d : F) (input rho) (input rho)) * eval rho inverse := by
''' + ''.join(product(label) for label in ('crossLeft', 'crossRight', 'xTimesMinus', 'xOutput'))
        cross_sum = selected['xTimesMinus'][2]
        source += f'''  have total := Compiler.checked_add_sound rho
    {linear(selected['crossLeft'][4])} {linear(selected['crossRight'][4])} {linear(cross_sum)} (by decide)
  rw [xTimesMinusProduct,total,crossLeftProduct,crossRightProduct,minus_value rho one four satisfied] at xOutputProduct
  change (output rho).x = _ at xOutputProduct
  calc
    _ = _ := xOutputProduct
    _ = _ := by unfold Group.cross input inverse; ring

theorem y_value {common} :
    (output rho).y = Group.diagonal (input rho) (input rho) *
      (1 + Group.delta (RuntimeJubjub.d : F) (input rho) (input rho)) * eval rho inverse := by
''' + ''.join(product(label) for label in ('xx', 'yy', 'yTimesPlus', 'yOutput'))
        source += f'''  have total := Compiler.checked_add_sound rho yy xx {linear(combine(plan['yy'], plan['xx']))} (by decide)
  rw [yTimesPlusProduct,total,xxProduct,yyProduct,plus_value rho one four satisfied] at yOutputProduct
  change (output rho).y = _ at yOutputProduct
  calc
    _ = _ := yOutputProduct
    _ = _ := by unfold Group.diagonal input inverse; ring

theorem double_sound {common}
    (valid : Group.OnCurve (RuntimeJubjub.d : F) (input rho))
    (nonSquare : Group.NoUnitSquare (RuntimeJubjub.d : F)) :
    output rho = Group.affineAdd (RuntimeJubjub.d : F) (input rho) (input rho) ∧
      Group.OnCurve (RuntimeJubjub.d : F) (output rho) := by
  exact Group.shared_inverse_double_sound (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    (eval rho inverse) nonSquare RuntimeJubjub.imaginary_square (input rho) (output rho) valid
    (inverse_row rho one four satisfied) (x_value rho one four satisfied) (y_value rho one four satisfied)
'''
        exports += ['delta_value', 'plus_value', 'minus_value', 'inverse_row', 'x_value', 'y_value', 'double_sound']
        source += ''.join('#print axioms ' + export + '\n' for export in exports)
        modules[name] = _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
    return modules


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import _signature_audits
    # Strict source/row validation includes all three actual output coordinates.
    doubles = generate_doubles(data, extracted, accepted_roles)
    deps = ['RuntimeTransferAssetMapImageCurve', *doubles]
    name = 'RuntimeTransferAssetMapCofactor'
    source = ''.join('import ShielddSecurity.' + dep + '\n' for dep in deps)
    source += f'''set_option maxHeartbeats 300000
namespace ShielddSecurity.{name}
def rawRows : List Row := ''' + ' ++ '.join(dep + '.rawRows' for dep in deps) + '\n'
    exports = []
    for offset, dependency in enumerate(deps):
        export = 'included' + str(offset)
        source += f'''theorem {export} : ∀ row ∈ {dependency}.rawRows, row ∈ rawRows := by
  intro row member
  simp only [rawRows,List.mem_append]
  tauto
'''
        exports.append(export)
    source += '''theorem actual_cofactor {F : Type} [Field F] [CharP F Scalar.modulus]
    [Fintype F] [DecidableEq F] (cardinality : Fintype.card F = Scalar.modulus)
    {J : Type} [AddCommGroup J] (model : Group.StandardCurveModel J (RuntimeJubjub.d : F))
    (standardOrder : ∀ point : J, (8 * Scalar.order) • point = 0)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    ∃ represented : J, model.coordinates represented = RuntimeTransferAssetMapDouble2.output rho ∧
      Scalar.order • represented = 0 := by
  have valid := RuntimeTransferAssetMapImageCurve.image_on_curve rho one four
    (fun row member => satisfied row (included0 row member))
  have first := RuntimeTransferAssetMapDouble0.double_sound rho one four
    (fun row member => satisfied row (included1 row member)) valid (RuntimeJubjub.nonsquare cardinality)
  have second := RuntimeTransferAssetMapDouble1.double_sound rho one four
    (fun row member => satisfied row (included2 row member)) first.2 (RuntimeJubjub.nonsquare cardinality)
  have third := RuntimeTransferAssetMapDouble2.double_sound rho one four
    (fun row member => satisfied row (included3 row member)) second.2 (RuntimeJubjub.nonsquare cardinality)
  exact Group.cofactor_image_annihilated (RuntimeJubjub.d : F) model Scalar.order standardOrder
    (RuntimeTransferAssetMapDouble0.input rho) (RuntimeTransferAssetMapDouble0.output rho)
    (RuntimeTransferAssetMapDouble1.output rho) (RuntimeTransferAssetMapDouble2.output rho)
    valid first.1 second.1 third.1
'''
    exports.append('actual_cofactor')
    source += ''.join('#print axioms ' + export + '\n' for export in exports)
    return name, _signature_audits(source + 'end ShielddSecurity.' + name + '\n')


def generate_native(data, extracted, accepted_roles):
    from . import transfer_asset_map_native as native
    from .generate_hash_round import _signature_audits
    cofactor_name, _ = generate(data, extracted, accepted_roles)
    native_name, _ = native.generate(data, extracted, accepted_roles)
    name = 'RuntimeTransferAssetMapNativeCofactor'
    source = f'''import ShielddSecurity.{cofactor_name}
import ShielddSecurity.{native_name}
import ShielddSecurity.GroupNativeCofactor
set_option maxHeartbeats 300000
namespace ShielddSecurity.{name}
def rawRows : List Row := {cofactor_name}.rawRows ++ {native_name}.rawRows

theorem native_cofactor {{F : Type}} [Field F] [CharP F Scalar.modulus] [Fintype F] [DecidableEq F]
    (codec : TransferReduction.CanonicalField F) (cardinality : Fintype.card F = Scalar.modulus)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows)
    (nativeOption : Bool) (nativeY : F)
    (sqrtSpecification : nativeOption = true ↔ ∃ root : F, root * root = eval rho RuntimeTransferAssetMapChoice.gx1)
    (nativeSquare : nativeY * nativeY = if nativeOption then eval rho RuntimeTransferAssetMapChoice.gx1
      else eval rho RuntimeTransferAssetMapChoice.gx2)
    (nativeParity : codec.decode nativeY % 2 = if nativeOption then 1 else 0) :
    RuntimeTransferAssetMapDouble2.output rho = GroupNativeCofactor.nativeEight (RuntimeJubjub.d : F)
      (Elligator.rationalPoint
        ((RuntimeElligatorAlgebra.k : F) * RuntimeTransferAssetMapNativeRoot.nativeSelectedX rho nativeOption)
        ((RuntimeElligatorAlgebra.k : F) * nativeY)) := by
  have cofactorRows : Satisfies rho {cofactor_name}.rawRows :=
    fun row member => satisfied row (List.mem_append.mpr (Or.inl member))
  have nativeRows : Satisfies rho {native_name}.rawRows :=
    fun row member => satisfied row (List.mem_append.mpr (Or.inr member))
  have nonSquare := RuntimeJubjub.nonsquare (F := F) cardinality
  have valid := RuntimeTransferAssetMapImageCurve.image_on_curve rho one four
    (fun row member => cofactorRows row ({cofactor_name}.included0 row member))
  have first := RuntimeTransferAssetMapDouble0.double_sound rho one four
    (fun row member => cofactorRows row ({cofactor_name}.included1 row member)) valid nonSquare
  have second := RuntimeTransferAssetMapDouble1.double_sound rho one four
    (fun row member => cofactorRows row ({cofactor_name}.included2 row member)) first.2 nonSquare
  have third := RuntimeTransferAssetMapDouble2.double_sound rho one four
    (fun row member => cofactorRows row ({cofactor_name}.included3 row member)) second.2 nonSquare
  have nativeFirst := (GroupFixedWindows.native_add_affine (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    nonSquare RuntimeJubjub.imaginary_square _ _ valid valid).trans first.1.symm
  have nativeSecond := (GroupFixedWindows.native_add_affine (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    nonSquare RuntimeJubjub.imaginary_square _ _ first.2 first.2).trans second.1.symm
  have nativeThird := (GroupFixedWindows.native_add_affine (RuntimeJubjub.d : F) RuntimeJubjub.imaginary
    nonSquare RuntimeJubjub.imaginary_square _ _ second.2 second.2).trans third.1.symm
  change GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
    (RuntimeTransferAssetMapDouble0.input rho) (RuntimeTransferAssetMapDouble0.input rho) =
    RuntimeTransferAssetMapDouble0.output rho at nativeFirst
  change GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
    (RuntimeTransferAssetMapDouble0.output rho) (RuntimeTransferAssetMapDouble0.output rho) =
    RuntimeTransferAssetMapDouble1.output rho at nativeSecond
  change GroupFixedWindows.nativeAdd (RuntimeJubjub.d : F)
    (RuntimeTransferAssetMapDouble1.output rho) (RuntimeTransferAssetMapDouble1.output rho) =
    RuntimeTransferAssetMapDouble2.output rho at nativeThird
  have recurrence : GroupNativeCofactor.nativeEight (RuntimeJubjub.d : F)
      (RuntimeTransferAssetMapDouble0.input rho) = RuntimeTransferAssetMapDouble2.output rho := by
    unfold GroupNativeCofactor.nativeEight
    dsimp only
    rw [nativeFirst,nativeSecond,nativeThird]
  have image := {native_name}.native_image codec cardinality rho one four nativeRows
    nativeOption nativeY sqrtSpecification nativeSquare nativeParity
  change RuntimeTransferAssetMapDouble0.input rho = _ at image
  rw [image] at recurrence
  exact recurrence.symm
#print axioms native_cofactor
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
