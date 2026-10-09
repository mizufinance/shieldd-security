"""Small field certificates for each branch's fixed rational map and doubles."""
import re

SQ = 'NativeEncryptionInitializationSquares'
AR = 'NativeEncryptionFixedArithmetic'
CO = 'RuntimeNativeEncryptionInitializationCoefficients'
CASTS = ('Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, '
         'Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero')


def checked(expression, result, indent='  '):
    return (f'{indent}have checked := {SQ}.polynomial_certificate (F := F)\n'
            f'{indent}  ({expression} : Int) {result} (by decide)\n'
            f'{indent}simpa only [{CASTS}] using checked\n')


def finish(body, namespace, names):
    body += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n'
                    for name in names)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', body)
    return body + f'end ShielddSecurity.{namespace}\n'


def header(namespace, imports):
    return (''.join(f'import ShielddSecurity.{name}\n' for name in imports) +
            'set_option maxHeartbeats 250000\nset_option maxRecDepth 2048\n' +
            f'namespace ShielddSecurity.{namespace}\n' +
            'variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]\n')


def generate(witnesses):
    p = int(witnesses['modulus'])
    assert p == 52435875175126190479447740508185965837690552500527637822603658699938581184513
    k, ik = witnesses['coefficient_k'], witnesses['inverse_k']
    c1, c2 = witnesses['coefficient_c1'], witnesses['coefficient_c2']
    d, iden = witnesses['coefficient_d'], witnesses['inverse_10241']
    assert (-40964 * ik) % p == 1 and 10241 * iden % p == 1
    body = header(CO, [SQ])
    body += ('def coefficientD {F : Type} [Field F] : F := -10240 / 10241\n'
             f'theorem k_value : (NativeAssetMap.coefficientK : F) = ({k} : F) := by\n')
    body += '  unfold NativeAssetMap.coefficientK\n' + checked('-40964', k)
    body += (f'theorem k_inverse : (NativeAssetMap.coefficientK : F)⁻¹ = ({ik} : F) := by\n'
             f'  have checked := {AR}.inverse_value (F := F) (-40964) {ik} (by decide)\n'
             f'  simpa only [NativeAssetMap.coefficientK, {CASTS}] using checked\n')
    body += (f'theorem c1_value : (NativeAssetMap.coefficientC1 : F) = ({c1} : F) := by\n'
             '  rw [NativeAssetMap.coefficientC1, k_inverse]\n')
    body += checked(f'40962 * {ik}', c1)
    body += (f'theorem c2_value : (NativeAssetMap.coefficientC2 : F) = ({c2} : F) := by\n'
             '  rw [NativeAssetMap.coefficientC2, k_inverse]\n')
    body += checked(f'{ik} * {ik}', c2)
    body += (f'theorem denominator_inverse : (10241 : F)⁻¹ = ({iden} : F) := by\n'
             f'  have checked := {AR}.inverse_value (F := F) 10241 {iden} (by decide)\n'
             f'  simpa only [{CASTS}] using checked\n')
    body += (f'theorem d_value : (coefficientD : F) = ({d} : F) := by\n'
             '  rw [coefficientD, div_eq_mul_inv, denominator_inverse]\n')
    body += checked(f'-10240 * {iden}', d)
    body += ('theorem edwards_equation : (NativeAssetMap.coefficientK : F) * coefficientD = 40960 := by\n'
             '  rw [k_value, d_value]\n')
    body += checked(f'{k} * {d}', 40960)
    body += ('theorem d_from_edwards (actual : F)\n'
             '    (equation : (NativeAssetMap.coefficientK : F) * actual = 40960) :\n'
             '    actual = coefficientD := by\n'
             '  have nonzero : (NativeAssetMap.coefficientK : F) ≠ 0 := by\n'
             '    rw [k_value]\n'
             f'    exact {AR}.cast_nonzero {k} (by decide) (by decide)\n'
             '  apply mul_left_cancel₀ nonzero\n'
             '  exact equation.trans edwards_equation.symm\n')
    param_names = ['k_value', 'k_inverse', 'c1_value', 'c2_value', 'denominator_inverse',
                   'd_value', 'edwards_equation', 'd_from_edwards']
    modules = {CO: finish(body, CO, param_names)}
    audits = {CO: param_names}
    assert [(r['domain'], r['branch']) for r in witnesses['records']] == [
        (28, False), (28, True), (29, False), (29, True)]
    for row in witnesses['records']:
        domain, branch = row['domain'], row['branch']
        namespace = f'RuntimeNativeEncryptionInitialization{domain}{"True" if branch else "False"}'
        u, first, cubic = row['hash'], row['first_x'], row['first_cubic']
        fi, s, ts = row['first_inverse'], row['s'], row['t_square']
        square, ip, it = row['selected_square'], row['plus_inverse'], row['square_inverse']
        states, doubles = row['states'], row['doubles']
        assert len(states) == 4 and len(doubles) == 3
        body = header(namespace, [CO])
        for name, count, values in (
            ('xSquares', 4, [v['x_square'] for v in states]),
            ('yValues', 4, [v['y'] for v in states]),
            ('inverses', 3, [v['inverse'] for v in doubles])):
            body += f'def {name} : Fin {count} → F := fun index => match index.val with\n'
            body += ''.join(f'  | {i} => {n}\n' for i, n in enumerate(values))
            body += '  | _ => 0\n'
        body += (f'theorem first_x : ElligatorNativeProgram.firstX NativeAssetMap.coefficientC1\n'
                 f'    ({u} : F) = ({first} : F) := by\n'
                 f'  have inverse : (1 + 5 * ({u} : F) * ({u} : F))⁻¹ = ({fi} : F) := by\n'
                 f'    have checked := {AR}.inverse_value (F := F) (1 + 5 * {u} * {u}) {fi} (by decide)\n'
                 f'    simpa only [{CASTS}] using checked\n'
                 f'  rw [ElligatorNativeProgram.firstX, {CO}.c1_value, inverse]\n')
        body += checked(f'-{c1} * {fi}', first)
        body += (f'theorem first_cubic : ElligatorNativeProgram.firstCubic NativeAssetMap.coefficientC1\n'
                 f'    NativeAssetMap.coefficientC2 ({u} : F) = ({cubic} : F) := by\n'
                 f'  rw [ElligatorNativeProgram.firstCubic, Elligator.cubic, first_x,\n'
                 f'    {CO}.c1_value, {CO}.c2_value]\n')
        body += checked(f'(({first} + {c1}) * {first} + {c2}) * {first}', cubic)
        body += (f'theorem rational_initial (root : F) (rootSquare : root * root = ({square} : F)) :\n'
                 f'    let point := Elligator.rationalPoint ({s} : F) (({k} : F) * root)\n'
                 '    point.x * point.x = xSquares 0 ∧ point.y = yValues 0 := by\n'
                 f'  have square : (({k} : F) * root) * (({k} : F) * root) = ({ts} : F) := by\n'
                 '    calc\n'
                 f'      _ = ({k} : F) * ({k} : F) * (root * root) := by ring\n'
                 f'      _ = ({k} : F) * ({k} : F) * ({square} : F) := by rw [rootSquare]\n'
                 '      _ = _ := by\n')
        body += checked(f'{k} * {k} * {square}', ts, '        ')
        body += (f'  have plusUnit : (({s} : F) + 1) * ({ip} : F) = 1 := by\n')
        body += checked(f'({s} + 1) * {ip}', 1, '    ')
        body += f'  have squareUnit : ({ts} : F) * ({it} : F) = 1 := by\n'
        body += checked(f'{ts} * {it}', 1, '    ')
        body += (f'  have initial := {SQ}.rational_squares ({s} : F) (({k} : F) * root)\n'
                 f'    ({ts} : F) ({ip} : F) ({it} : F) square plusUnit squareUnit\n'
                 '  refine ⟨initial.1.trans ?_, initial.2.trans ?_⟩\n'
                 '  · change _ = _\n')
        body += checked(f'{s} * {s} * {it}', states[0]['x_square'], '    ')
        body += '  · change _ = _\n'
        body += checked(f'({s} - 1) * {ip}', states[0]['y'], '    ')
        body += (f'theorem steps (index : Fin 3) :\n'
                 '    let next : Fin 4 := ⟨index.val + 1, by omega⟩\n'
                 f'    ((1 + ({CO}.coefficientD : F) * xSquares index.castSucc * yValues index.castSucc * yValues index.castSucc) *\n'
                 f'      (1 - ({CO}.coefficientD : F) * xSquares index.castSucc * yValues index.castSucc * yValues index.castSucc)) * inverses index = 1 ∧\n'
                 f'    (2 * yValues index.castSucc * (1 - ({CO}.coefficientD : F) * xSquares index.castSucc * yValues index.castSucc * yValues index.castSucc) * inverses index) *\n'
                 f'      (2 * yValues index.castSucc * (1 - ({CO}.coefficientD : F) * xSquares index.castSucc * yValues index.castSucc * yValues index.castSucc) * inverses index) *\n'
                 '        xSquares index.castSucc = xSquares next ∧\n'
                 '    (yValues index.castSucc * yValues index.castSucc + xSquares index.castSucc) *\n'
                 f'      (1 + ({CO}.coefficientD : F) * xSquares index.castSucc * yValues index.castSucc * yValues index.castSucc) *\n'
                 '        inverses index = yValues next := by\n'
                 '  fin_cases index\n')
        for i, witness in enumerate(doubles):
            a, b, iv = states[i]['x_square'], states[i]['y'], witness['inverse']
            delta = f'{d} * {a} * {b} * {b}'
            expressions = [
                (f'(1 + {delta}) * (1 - {delta}) * {iv}', 1),
                (f'(2 * {b} * (1 - {delta}) * {iv}) * (2 * {b} * (1 - {delta}) * {iv}) * {a}',
                 states[i+1]['x_square']),
                (f'({b} * {b} + {a}) * (1 + {delta}) * {iv}', states[i+1]['y'])]
            body += f'  · simp only [xSquares, yValues, inverses, {CO}.d_value]\n'
            body += '    refine ⟨?_, ?_, ?_⟩\n'
            for expression, result in expressions:
                body += '    · ' + checked(expression, result, '      ').lstrip()
        body += (f'theorem nonzero (root : F) (rootSquare : root * root = ({square} : F)) :\n'
                 f'    (GroupNativeCofactor.nativeEight {CO}.coefficientD\n'
                 f'      (Elligator.rationalPoint ({s} : F) (({k} : F) * root))).x ≠ 0 := by\n'
                 f'  apply {SQ}.three_double_nonzero {CO}.coefficientD\n'
                 f'    (Elligator.rationalPoint ({s} : F) (({k} : F) * root)) xSquares yValues inverses\n'
                 '    (rational_initial root rootSquare) steps\n'
                 f'  exact {AR}.cast_nonzero {states[3]["x_square"]} (by decide) (by decide)\n')
        names = ['first_x', 'first_cubic', 'rational_initial', 'steps', 'nonzero']
        modules[namespace] = finish(body, namespace, names)
        audits[namespace] = names
    assert len(modules) == 5 and sum(map(len, audits.values())) == 28
    return modules, audits
