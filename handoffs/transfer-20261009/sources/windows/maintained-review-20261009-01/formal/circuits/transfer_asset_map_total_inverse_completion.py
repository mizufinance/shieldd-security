"""Actual total-inverse zero/nonzero local ownership/constructor recipe.

The denominator is an already-built source LC. This local construction covers
the zero flag, inverse, all three exact product pairs/assertions and constant
link. Surrounding map rows are not assumed to survive these owned writes.
"""
from . import transfer_asset_map as maps, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def plan(data, extracted, accepted_roles):
    from .transfer_asset_map_completion import _unit
    result = maps.certificates(data, extracted, accepted_roles)
    checked, raw, rows = result['checked'], result['raw'], result['rows']
    v = checked['values'];copy = checked['metadata']['constant_copy']
    inverse, zero = _unit(v['inv'], 'total inverse'), _unit(v['zero'], 'total zero')
    if inverse == zero:
        raise relation.RelationError('map total inverse seed alias')
    protected = {0, 1, 2, copy}
    for lc in (checked['asset'], checked['hash'], v['u'], *accepted_roles['observed'].values()):
        protected.update(c for c, _ in lc)
    if protected & {inverse, zero} or any(c in (inverse, zero) for c, _ in v['den']):
        raise relation.RelationError('map total inverse seeds alias denominator/shared input')
    pairs = []
    indices = set()
    owned = {inverse, zero}
    for label, a, b, output, target in (
            ('unit', v['den'], v['inv'], checked['products'][1], combine(maps.ONE, v['zero'], -1)),
            ('denZero', v['den'], v['zero'], checked['products'][2], ()),
            ('invZero', v['inv'], v['zero'], checked['products'][3], ())):
        cert = arithmetic.product_certificate(a, b, output, rows)
        if cert['kind'] != 'product':
            raise relation.RelationError('map total inverse exact two-row product lowering required')
        if cert.get('swapped'):
            a, b = b, a
        auxiliary = _unit(cert['auxiliary'], label + ' auxiliary')
        if auxiliary in owned or auxiliary in protected:
            raise relation.RelationError('map total inverse auxiliary alias')
        excluded = protected | owned | {auxiliary} | {c for c, _ in a + b}
        pivots = [c for c, n in output if n == 1 and c not in excluded]
        if len(pivots) > 1:
            raise relation.RelationError('map total inverse ambiguous product pivot')
        if not pivots and output != target:
            raise relation.RelationError('map total inverse unsupported fused target')
        pivot = pivots[0] if pivots else None
        remainder = tuple((c, n) for c, n in output if c != pivot) if pivot is not None else ()
        writes = [auxiliary] + ([pivot] if pivot is not None else [])
        if set(writes) & owned:
            raise relation.RelationError('map total inverse repeated product write')
        owned.update(writes);indices.update(cert['rows'])
        difference = combine(output, target, -1)
        assertion = None
        if difference:
            matches = [i for i, row in rows.items()
                       if row in ((difference, ()), (maps._scale(difference, -1), ()))]
            if len(matches) != 1:
                raise relation.RelationError('map total inverse exact original product assertion')
            assertion = matches[0];indices.add(assertion)
        pairs.append(dict(label=label, left=a, right=b, output=output, target=target,
                          pivot=pivot, remainder=remainder, auxiliary=auxiliary,
                          rows=cert['rows'], assertion=assertion))
    material = owned - {inverse, zero}
    if any(c in material for pair in pairs for lc in (pair['left'], pair['right'], pair['remainder']) for c, _ in lc):
        raise relation.RelationError('map total inverse material writes affect source/remainders')
    if any(c in owned for c, _ in v['den']):
        raise relation.RelationError('map total inverse writes affect denominator')
    boolean = [i for i, row in rows.items() if row == (v['zero'], v['zero'])]
    link = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(boolean) != 1 or len(link) != 1:
        raise relation.RelationError('map total inverse exact zero Boolean/constant link')
    indices.update(boolean + link)
    return dict(checked=checked, inverse=inverse, zero=zero, pairs=pairs,
                raw={i: raw[i] for i in sorted(indices)}, normalized={i: rows[i] for i in sorted(indices)},
                owned_writes=sorted(owned), denominator=v['den'], boolean_row=boolean[0], link_row=link[0])


def construct(data, extracted, accepted_roles, base):
    """Bounded runtime construction check for ANY already-built denominator."""
    recipe = plan(data, extracted, accepted_roles)
    p = maps.P;rho = dict(base)
    evaluate = lambda lc: sum(rho.get(c, 0) * n for c, n in lc) % p
    if rho.get(0) != 1 or rho.get(recipe['checked']['metadata']['constant_copy']) != 1:
        raise relation.RelationError('map total inverse kept constant/copy must be one')
    denominator = evaluate(recipe['denominator'])
    rho[recipe['inverse']] = pow(denominator, -1, p) if denominator else 0
    rho[recipe['zero']] = int(denominator == 0)
    for pair in recipe['pairs']:
        left, right, target = evaluate(pair['left']), evaluate(pair['right']), evaluate(pair['target'])
        rho[pair['auxiliary']] = (left - right)**2 % p
        if pair['pivot'] is not None:
            rho[pair['pivot']] = (target - evaluate(pair['remainder'])) % p
        if left * right % p != target:
            raise relation.RelationError('map total inverse native branch equation failed')
    if any(evaluate(a)**2 % p != evaluate(b) for a, b in recipe['raw'].values()):
        raise relation.RelationError('map total inverse original row failed')
    if any(rho.get(c, 0) != value for c, value in base.items() if c not in recipe['owned_writes']):
        raise relation.RelationError('map total inverse changed column outside exact ownership')
    return dict(assignment=rho, plan=recipe, proof=False,
                scope='runtime exact local total inverse rows; source algebra/kernel/full Transfer open')


def generate(data, extracted, accepted_roles):
    """Construct the exact local original rows without an inverse/nonzero premise.

    Materialized products retain their original unit pivots. Fused targets own
    only their difference-square auxiliary. The bounded signed row certificate
    covers both physical orientations and the kept outlined constant link.
    """
    from .generate_hash_round import linear, _signature_audits
    recipe = plan(data, extracted, accepted_roles)
    name = 'RuntimeTransferAssetMapTotalInverseCompletion'
    copy = recipe['checked']['metadata']['constant_copy']
    inverse, zero = recipe['inverse'], recipe['zero']
    material = [c for c in recipe['owned_writes'] if c not in (inverse, zero)]
    den = linear(recipe['denominator'])
    pairs = recipe['pairs']
    declarations = []
    values = []
    for i, pair in enumerate(pairs):
        for label in ('left', 'right', 'output', 'target', 'remainder'):
            declarations.append(f'def {label}{i} : Linear := {linear(pair[label])}\n')
        declarations.append(f'''def pairRows{i} : List Row := [
  ⟨Compiler.subtract left{i} right{i},[({pair['auxiliary']},1)]⟩,
  ⟨left{i} ++ right{i},[({pair['auxiliary']},1)] ++ scaleLinear 4 output{i}⟩,
  ⟨Compiler.subtract output{i} target{i},[]⟩]
''')
        values.append((pair['auxiliary'], f'(eval (seedAssignment rho) left{i} - eval (seedAssignment rho) right{i}) ^ 2'))
        if pair['pivot'] is not None:
            values.append((pair['pivot'], f'eval (seedAssignment rho) target{i} - eval (seedAssignment rho) remainder{i}'))
    value_body = 'rho column'
    for column, value in reversed(values):
        value_body = f'if column = {column} then {value} else {value_body}'
    out = [f'''import ShielddSecurity.Elligator
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact source metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Local total inverse only. No surrounding map/Transfer row survival claim.
def modulus : Nat := {maps.P}
def denominator : Linear := {den}
def seedWrites : List Nat := [{inverse},{zero}]
def materialWrites : List Nat := {material}
def ownedWrites : List Nat := seedWrites ++ materialWrites
def originalRows : List Nat := {list(recipe['raw'])}
def rawRows : List Row := [
''' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩' for a, b in recipe['raw'].values()) + ''']
variable {F : Type} [Field F] [DecidableEq F]
def nativeInverse (rho : Nat → F) : F :=
  if eval rho denominator = 0 then 0 else (eval rho denominator)⁻¹
def nativeZero (rho : Nat → F) : F :=
  if eval rho denominator = 0 then 1 else 0
def seedAssignment (rho : Nat → F) : Nat → F :=
  patchAssignment rho (fun column => if column = ''' + str(inverse) + ''' then nativeInverse rho else nativeZero rho) seedWrites
''' + ''.join(declarations) + f'''
def materialValues (rho : Nat → F) (column : Nat) : F := {value_body}
def completeAssignment (rho : Nat → F) : Nat → F :=
  patchAssignment (seedAssignment rho) (materialValues rho) materialWrites
def expectedRows : List Row := pairRows0 ++ pairRows1 ++ pairRows2 ++
  [booleanRow {zero},⟨[],[]⟩]

theorem ownership_checked : (seedWrites ++ materialWrites).Nodup := by decide

theorem preserves (rho : Nat → F) (column : Nat) (outside : column ∉ ownedWrites) :
    completeAssignment rho column = rho column := by
  simp only [ownedWrites,List.mem_append,not_or] at outside
  exact (patchAssignment_preserves (seedAssignment rho) (materialValues rho) materialWrites column outside.2).trans
    (patchAssignment_preserves rho _ seedWrites column outside.1)

theorem material_eval (rho : Nat → F) (terms : Linear)
    (fresh : ∀ term ∈ terms, term.1 ∉ materialWrites) :
    eval (completeAssignment rho) terms = eval (seedAssignment rho) terms := by
  apply eval_agrees
  intro term member
  exact patchAssignment_preserves (seedAssignment rho) (materialValues rho)
    materialWrites term.1 (fresh term member)

theorem denominator_value (rho : Nat → F) :
    eval (completeAssignment rho) denominator = eval rho denominator := by
  apply eval_agrees
  intro term member
  exact preserves rho term.1 (by
    have checked : denominator.all (fun term => decide (term.1 ∉ ownedWrites)) = true := by decide
    exact of_decide_eq_true ((List.all_eq_true.mp checked) term member))

theorem inverse_value (rho : Nat → F) : completeAssignment rho {inverse} = nativeInverse rho := by
  simp [completeAssignment,patchAssignment,materialWrites,seedAssignment,seedWrites]

theorem zero_value (rho : Nat → F) : completeAssignment rho {zero} = nativeZero rho := by
  simp [completeAssignment,patchAssignment,materialWrites,seedAssignment,seedWrites]

theorem native_equations (rho : Nat → F) :
    eval rho denominator * nativeInverse rho = 1 - nativeZero rho ∧
    eval rho denominator * nativeZero rho = 0 ∧ nativeInverse rho * nativeZero rho = 0 :=
  Elligator.inverse_constraints_complete (eval rho denominator)
''']
    exports = ['ownership_checked', 'preserves', 'denominator_value', 'inverse_value', 'zero_value', 'native_equations']
    # Only three possible actual source inputs. These facts are derived from
    # the constructor and certified exact LC identities, never caller premises.
    source_symbols = {recipe['denominator']: 'eval rho denominator',
                      recipe['checked']['values']['inv']: 'nativeInverse rho',
                      recipe['checked']['values']['zero']: 'nativeZero rho'}
    for i, pair in enumerate(pairs):
        left_value, right_value = source_symbols[pair['left']], source_symbols[pair['right']]
        target = '1 - nativeZero rho' if i == 0 else '(0 : F)'
        out.append(f'''theorem pair_complete{i} [CharP F modulus] (rho : Nat → F) (one : rho 0 = 1) :
    Satisfies (completeAssignment rho) pairRows{i} := by
  have denValue := denominator_value rho
  have invValue := inverse_value rho
  have flagValue := zero_value rho
  have leftValue : eval (completeAssignment rho) left{i} = {left_value} := by
''')
        for label, lc, value in [('left', pair['left'], left_value), ('right', pair['right'], right_value)]:
            if label == 'right':
                out.append(f'  have rightValue : eval (completeAssignment rho) right{i} = {value} := by\n')
            if lc == recipe['denominator']:
                out.append(f'    exact denValue\n')
            else:
                unit = inverse if lc == recipe['checked']['values']['inv'] else zero
                equation = 'invValue' if unit == inverse else 'flagValue'
                out.append(f'''    have exactLC := Compiler.canonical_equal (completeAssignment rho) {label}{i} [({unit},1)] (by decide)
    simpa only [eval,Int.cast_one,one_mul,add_zero,{equation}] using exactLC
''')
        out.append(f'''  have targetSeed : eval (seedAssignment rho) target{i} = {target} := by
''')
        if i == 0:
            out.append(f'''    have exactLC := Compiler.canonical_equal (seedAssignment rho) target{i}
      [(0,1),({zero},-1)] (by decide)
    have seedOne : seedAssignment rho 0 = 1 := by
      simp [seedAssignment,seedWrites,patchAssignment,one]
    have seedZero : seedAssignment rho {zero} = nativeZero rho := by
      simp [seedAssignment,seedWrites,patchAssignment]
    simpa only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,
      seedOne,seedZero,sub_eq_add_neg] using exactLC
''')
        else:
            out.append(f'    rfl\n')
        out.append(f'''  have targetFresh : ∀ term ∈ target{i}, term.1 ∉ materialWrites := by
    have checked : target{i}.all (fun term => decide (term.1 ∉ materialWrites)) = true := by decide
    intro term member
    exact of_decide_eq_true ((List.all_eq_true.mp checked) term member)
  have targetValue : eval (completeAssignment rho) target{i} = {target} :=
    (material_eval rho target{i} targetFresh).trans targetSeed
  have outputValue : eval (completeAssignment rho) output{i} = {target} := by
''')
        if pair['pivot'] is None:
            out.append(f'    exact targetValue\n')
        else:
            out.append(f'''    have remainderFresh : ∀ term ∈ remainder{i}, term.1 ∉ materialWrites := by
      have checked : remainder{i}.all (fun term => decide (term.1 ∉ materialWrites)) = true := by decide
      intro term member
      exact of_decide_eq_true ((List.all_eq_true.mp checked) term member)
    have remainderValue := material_eval rho remainder{i} remainderFresh
    have outputLC := Compiler.canonical_equal (completeAssignment rho) output{i}
      ([({pair['pivot']},1)] ++ remainder{i}) (by decide)
    have pivotValue : completeAssignment rho {pair['pivot']} =
        eval (seedAssignment rho) target{i} - eval (seedAssignment rho) remainder{i} := by
      simp [completeAssignment,patchAssignment,materialWrites,materialValues]
    rw [outputLC,eval_append]
    simp only [eval,Int.cast_one,one_mul,add_zero,pivotValue,remainderValue,targetSeed]
    ring
''')
        out.append(f'''  have leftSeed : eval (seedAssignment rho) left{i} = {left_value} := by
    rw [← material_eval rho left{i} (by
      have checked : left{i}.all (fun term => decide (term.1 ∉ materialWrites)) = true := by decide
      intro term member
      exact of_decide_eq_true ((List.all_eq_true.mp checked) term member))]
    exact leftValue
  have rightSeed : eval (seedAssignment rho) right{i} = {right_value} := by
    rw [← material_eval rho right{i} (by
      have checked : right{i}.all (fun term => decide (term.1 ∉ materialWrites)) = true := by decide
      intro term member
      exact of_decide_eq_true ((List.all_eq_true.mp checked) term member))]
    exact rightValue
  have auxiliaryValue : completeAssignment rho {pair['auxiliary']} =
      ({left_value} - {right_value}) ^ 2 := by
    simp [completeAssignment,patchAssignment,materialWrites,materialValues,leftSeed,rightSeed]
  have productValue : {left_value} * {right_value} = {target} := by
    simpa only [mul_comm] using (native_equations rho){('.1' if i == 0 else '.2.1' if i == 1 else '.2.2')}
  intro row member
  simp only [pairRows{i},List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · simp only [Square,Compiler.eval_subtract,eval,Int.cast_one,one_mul,add_zero,
      leftValue,rightValue,auxiliaryValue]
    ring
  · simp only [Square,eval_append,eval_scale,eval,Int.cast_one,one_mul,add_zero,
      Int.cast_ofNat,leftValue,rightValue,outputValue,auxiliaryValue]
    calc
      _ = ({left_value} - {right_value}) ^ 2 + 4 * ({left_value} * {right_value}) := by ring
      _ = _ := by rw [productValue]
  · simp only [Square,Compiler.eval_subtract,outputValue,targetValue,sub_self,zero_mul,eval]
''')
        exports.append('pair_complete' + str(i))
    out.append(f'''theorem coverage_checked : rawRows.all (fun actual =>
    expectedRows.any (fun expected => decide (
      (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
       Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide

theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem complete [CharP F modulus] (rho : Nat → F) (one : rho 0 = 1)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have expected : Satisfies (completeAssignment rho) expectedRows := by
    intro row member
    simp only [expectedRows,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with ((first | second) | third) | (rfl | rfl)
    · exact pair_complete0 rho one row first
    · exact pair_complete1 rho one row second
    · exact pair_complete2 rho one row third
    · have value := zero_value rho
      simp only [booleanRow,Square,eval,Int.cast_one,one_mul,add_zero,value]
      unfold nativeZero
      split <;> simp
    · simp only [Square,eval,zero_mul]
  have copyValue : completeAssignment rho {copy} = completeAssignment rho 0 := by
    rw [preserves rho {copy} (by decide),preserves rho 0 (by decide),linked]
  exact CompilerSignedCompletion.original_rows (completeAssignment rho) expectedRows rawRows
    {copy} copyValue expected coverage
''')
    exports.extend(['coverage_checked', 'coverage', 'complete'])
    out.extend('#print axioms ' + export + '\n' for export in exports)
    out.append('end ShielddSecurity.' + name + '\n')
    return name, _signature_audits(''.join(out))
