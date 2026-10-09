"""Original Boolean/reconstruction/comparison/cap rows -> IVK integer meaning.

The quotient-only mode is the initial development unit. Full mode also derives
the remainder bound, short quotient-eight interval and actual inverse relation.
All assignments satisfy one original collected row subset. Legal-input auxiliary
completion and full-family/caller composition remain separate obligations.
"""
import hashlib
from pathlib import Path
import sys

from generate_hash_round import linear, signed
from generate_scalar_chain import generate as generate_chains, product_data
from hash_rows import canonical, scaled
from poseidon_graph import P, decode_json
from scalar_rows import ORDER, select


def terminal_assertion_proof(certificate, output_name):
    target = linear(certificate['target'])
    delta = canonical(certificate['output'] + scaled(certificate['target'], -1))
    if certificate['assertion']['expression'] == delta:
        return f'Compiler.checked_assertion_sound rho rows {output_name} {target} normalized (by decide)'
    if certificate['assertion']['expression'] == scaled(delta, -1):
        return f'(Compiler.checked_assertion_sound rho rows {target} {output_name} normalized (by decide)).symm'
    raise ValueError('unsupported original terminal assertion orientation')


def generate(export, parameter_root, export_hash, quotient_only=False):
    comparison = 'quotient' if quotient_only else None
    selected = select(export, parameter_root, comparison)
    core = generate_chains(export, parameter_root, export_hash, comparison)
    core_used = {selected['constant_link']}
    for step in selected['steps']:
        if comparison is None or step['name'] == comparison:
            core_used.update(step['certificate'].get('rows', []))
    used = set(core_used)
    table = {}
    for index, pair in selected['rows'].items():
        normal = tuple(canonical((0 if c == selected['outline'] else c, v) for c, v in terms)
                       for terms in pair)
        table.setdefault(normal, index)
    names = ['quotient'] if quotient_only else ['quotient', 'remainder']
    for name in names:
        for bit in selected['bits'][name]:
            used.add(table[(bit, bit)])
        used.add(selected['range_rows'][name]['row'])
        used.add(selected['endings'][name]['row'])
    if not quotient_only:
        used.add(selected['equation']['row'])
        used.update(selected['last_guard'].get('rows', []))
        used.update(selected['nonzero'].get('rows', []))
        used.add(selected['last_guard']['assertion']['row'])
        used.add(selected['nonzero']['assertion']['row'])
    out = ['import ShielddSecurity.ScalarBits\n',
           core.removeprefix('import ShielddSecurity.ScalarRows\n'),
           '''\nnamespace ShielddSecurity.RuntimeScalarMeaning
def boundaryRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(selected['rows'][i][0]) + ', '
                         + linear(selected['rows'][i][1]) + '⟩' for i in sorted(used - core_used)))
    out.append(f''']
-- Both lanes read the same rho; duplicated ownership or an honest scalar is
-- never an extra theorem premise.
def rawRows : List Row := C.rawRows ++ boundaryRows
def rows : List Row := Compiler.unoutlineRows {selected['outline']} rawRows
theorem constantLink : Compiler.checkRow C.modulus rawRows
    ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ = true := by decide

theorem core_satisfied {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho rawRows) : Satisfies rho C.rawRows := by
  intro row member
  exact satisfied row (List.mem_append.mpr (Or.inl member))

theorem normalized_satisfied {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho rows :=
  Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied constantLink
''')
    maxima = {'quotient': 8, 'remainder': ORDER - 1, 'last': P - 1 - 8 * ORDER}
    for name in names:
        out.append(f'def {name}Bits : List Linear := ['
                   + ', '.join(linear(bit) for bit in selected['bits'][name]) + ']\n')
        out.append(f'def {name}Value : Linear := {linear(selected["roles"][name])}\n')
        out.append(f'''noncomputable def {name}Nat {{F : Type}} [Field F] (rho : Nat → F) : Nat :=
  binary (ScalarBits.decodeBits rho {name}Bits)

theorem {name}_value {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ({name}Nat rho : F) = eval rho {name}Value := by
  have normalized := normalized_satisfied rho satisfied
  have decoded := ScalarBits.decoded_bits_value rho rows normalized {name}Bits (by decide)
  have reconstruction : eval rho (ScalarBits.bitLinear {name}Bits) = eval rho {name}Value := by
''')
        expected = canonical(term for i, bit in enumerate(selected['bits'][name])
                             for term in scaled(bit, 2 ** i))
        delta = canonical(expected + scaled(selected['roles'][name], -1))
        expression = selected['range_rows'][name]['expression']
        if expression == delta:
            out.append(f'''    exact Compiler.checked_assertion_sound rho rows
      (ScalarBits.bitLinear {name}Bits) {name}Value normalized (by decide)
''')
        elif expression == scaled(delta, -1):
            out.append(f'''    exact (Compiler.checked_assertion_sound rho rows
      {name}Value (ScalarBits.bitLinear {name}Bits) normalized (by decide)).symm
''')
        else:
            raise ValueError('unsupported scalar reconstruction orientation')
        out.append('  exact decoded.symm.trans reconstruction\n')
    for name in ['quotient'] if quotient_only else ['quotient', 'remainder', 'last']:
        bit_name = 'remainder' if name == 'last' else name
        out.append(f'''
theorem {name}_final_meaning {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho C.{name}Final = (if {bit_name}Nat rho ≤ {maxima[name]} then 1 else 0) := by
  have normalized := normalized_satisfied rho satisfied
  have recurrence := C.{name}_actual_chain_sound rho one (core_satisfied rho satisfied)
  have decoded := ScalarBits.polynomial_chain_order rho rows normalized C.{name}Steps (by decide)
  have shape : C.{name}Steps.map ScalarRows.StepData.left = {bit_name}Bits := by decide
  have bits : C.{name}Steps.map (fun step => ScalarBits.decodeBit rho step.left) =
      ScalarBits.decodeBits rho {bit_name}Bits := by
    simpa only [ScalarBits.decodeBits, List.map_map] using
      congrArg (fun values : List Linear => values.map (ScalarBits.decodeBit rho)) shape
  have maximum : binary (C.{name}Steps.map ScalarRows.StepData.right) = {maxima[name]} := by decide
  rw [bits, maximum] at decoded
  exact recurrence.trans decoded
''')
        if name == 'last':
            continue
        ending = selected['endings'][name]
        delta = canonical(selected['roles'][f'{name}.comparison{len(selected["bits"][name]) - 1}'] + ((0, P - 1),))
        if ending['expression'] == delta:
            ending_proof = f'Compiler.checked_assertion_sound rho rows C.{name}Final [(0, 1)] normalized (by decide)'
        elif ending['expression'] == scaled(delta, -1):
            ending_proof = f'(Compiler.checked_assertion_sound rho rows [(0, 1)] C.{name}Final normalized (by decide)).symm'
        else:
            raise ValueError('unsupported scalar final assertion orientation')
        out.append(f'''
theorem {name}_bound {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    {name}Nat rho ≤ {maxima[name]} := by
  have normalized := normalized_satisfied rho satisfied
  have final : eval rho C.{name}Final = 1 := by
    simpa only [eval, one, mul_one, add_zero, Int.cast_one] using {ending_proof}
  exact ScalarBits.field_condition_true ({name}Nat rho ≤ {maxima[name]})
    (({name}_final_meaning rho one satisfied).symm.trans final)

#print axioms {name}_value
#print axioms {name}_final_meaning
#print axioms {name}_bound
''')
    if not quotient_only:
        # The two remaining product/one relations are original selected rows.
        guard_left = selected['bits']['quotient'][3]
        last = selected['roles']['last.comparison251']
        guard_right = canonical(((0, 1),) + scaled(last, -1))
        for name, terms in [('highBit', guard_left), ('guardRight', guard_right),
                            ('guardOutput', selected['last_guard']['output']),
                            ('inverseOutput', selected['nonzero']['output']),
                            ('hash', selected['roles']['value']), ('ivk', selected['roles']['ivk']),
                            ('inverse', selected['roles']['ivk_inverse'])]:
            out.append(f'def {name} : Linear := {linear(terms)}\n')
        out.append(f'''
theorem final_cap {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows)
    (lastQuotient : quotientNat rho = 8) : remainderNat rho ≤ {maxima['last']} := by
  have normalized := normalized_satisfied rho satisfied
  have high := ScalarBits.quotient_eight_high (ScalarBits.decodeBits rho quotientBits)
    (by simp only [ScalarBits.decodeBits, List.length_map, quotientBits,
      List.length_cons, List.length_nil]) lastQuotient
  have bit := ScalarBits.checked_bit_value rho rows normalized quotientBits (by decide)
    highBit (by decide)
  have decodedHigh : ScalarBits.decodeBit rho highBit =
      (ScalarBits.decodeBits rho quotientBits).getD 3 false := by rfl
  rw [decodedHigh, high] at bit
  have guardProduct := ScalarRows.checked_product_sound rho one (C.fourNonzero (F := F))
    rows normalized highBit guardRight guardOutput ({product_data(selected['last_guard'])}) (by decide)
  have guardAssertion : eval rho guardOutput = 0 := by
    simpa [eval] using ({terminal_assertion_proof(selected['last_guard'], 'guardOutput')})
  have guard : eval rho highBit * eval rho guardRight = 0 :=
    guardProduct.symm.trans guardAssertion
  have factor : eval rho guardRight = 1 - eval rho C.lastFinal := by
    have same := Compiler.canonical_equal rho guardRight
      ([(0, 1)] ++ scaleLinear (-1) C.lastFinal) (by decide)
    simpa [eval_append, eval_scale, eval, one, sub_eq_add_neg] using same
  have final : eval rho C.lastFinal = 1 := by
    rw [factor, bit] at guard
    exact (sub_eq_zero.mp (by simpa using guard)).symm
  exact ScalarBits.field_condition_true (remainderNat rho ≤ {maxima['last']})
    ((last_final_meaning rho one satisfied).symm.trans final)

theorem ivk_nonzero_relation {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    (remainderNat rho : F) * eval rho inverse = 1 := by
  have normalized := normalized_satisfied rho satisfied
  have multiplication := ScalarRows.checked_product_sound rho one (C.fourNonzero (F := F))
    rows normalized inverse ivk inverseOutput ({product_data(selected['nonzero'])}) (by decide)
  have asserted : eval rho inverseOutput = 1 := by
    simpa [eval, one] using ({terminal_assertion_proof(selected['nonzero'], 'inverseOutput')})
  rw [asserted] at multiplication
  have input : eval rho ivk = (remainderNat rho : F) := by
    have actual := Compiler.canonical_equal rho ivk (ScalarBits.bitLinear remainderBits) (by decide)
    exact actual.trans (ScalarBits.decoded_bits_value rho rows normalized remainderBits (by decide))
  rw [input] at multiplication
  simpa only [eval, one, mul_one, add_zero, Int.cast_one, mul_comm] using multiplication.symm
''')
        sum_terms = canonical(scaled(selected['roles']['quotient'], ORDER) + selected['roles']['remainder'])
        out.append(f'def reducedSum : Linear := {linear(sum_terms)}\n')
        delta = canonical(sum_terms + scaled(selected['roles']['value'], -1))
        if selected['equation']['expression'] == delta:
            equation_proof = 'Compiler.checked_assertion_sound rho rows reducedSum hash normalized (by decide)'
        elif selected['equation']['expression'] == scaled(delta, -1):
            equation_proof = '(Compiler.checked_assertion_sound rho rows hash reducedSum normalized (by decide)).symm'
        else:
            raise ValueError('unsupported scalar reduction equation orientation')
        out.append(f'''
theorem actual_reduction_representation {{F : Type}} [Field F] [CharP F C.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    ∃ value : Nat, value < Scalar.modulus ∧ (value : F) = eval rho hash ∧
      Scalar.Reduction value (quotientNat rho) (remainderNat rho) ∧ remainderNat rho ≠ 0 := by
  have normalized := normalized_satisfied rho satisfied
  have qBound := quotient_bound rho one satisfied
  have rBound : remainderNat rho < Scalar.order := by
    have bounded := remainder_bound rho one satisfied
    simp only [Scalar.order] at bounded ⊢
    omega
  have cap : quotientNat rho = 8 → remainderNat rho ≤ Scalar.lastRemainder := by
    intro lastQuotient
    simpa only [Scalar.lastRemainder, Scalar.modulus, Scalar.order] using
      final_cap rho one satisfied lastQuotient
  have arithmetic : eval rho reducedSum = eval rho hash := {equation_proof}
  have shape := Compiler.canonical_equal rho reducedSum
    (scaleLinear ({ORDER} : Int) quotientValue ++ remainderValue) (by decide)
  have equation : (quotientNat rho : F) * (Scalar.order : F) +
      (remainderNat rho : F) = eval rho hash := by
    rw [shape, eval_append, eval_scale, ← quotient_value rho satisfied,
      ← remainder_value rho satisfied] at arithmetic
    simpa [Scalar.order, mul_comm] using arithmetic
  exact Scalar.reduction_representation (eval rho hash) (eval rho inverse)
    (quotientNat rho) (remainderNat rho) qBound rBound cap equation
      (ivk_nonzero_relation rho one satisfied)

#print axioms last_final_meaning
#print axioms final_cap
#print axioms ivk_nonzero_relation
#print axioms actual_reduction_representation
''')
    out.append('''
#print axioms constantLink
#print axioms core_satisfied
#print axioms normalized_satisfied
end ShielddSecurity.RuntimeScalarMeaning
''')
    return ''.join(out).replace('C.', 'RuntimeScalarChains.')


if __name__ == '__main__':
    arguments = sys.argv[1:]
    quotient_only = bool(arguments and arguments[0] == '--quotient-only')
    if quotient_only:
        arguments = arguments[1:]
    path, runtime, output = arguments
    raw = Path(path).read_bytes()
    result = generate(decode_json(raw.decode('utf-8')),
                      Path(runtime) / 'crates/crypto/primitives/params',
                      hashlib.sha256(raw).hexdigest(), quotient_only)
    target = Path(output)
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(result, encoding='utf-8')
    temporary.replace(target)
