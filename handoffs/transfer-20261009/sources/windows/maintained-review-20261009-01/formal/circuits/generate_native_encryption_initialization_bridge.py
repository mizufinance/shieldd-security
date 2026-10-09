"""Join four checked square branches to the owned root APIs and SDK keys."""
from generate_native_encryption_initialization_squares import checked, finish

CO = 'RuntimeNativeEncryptionInitializationCoefficients'
NAME = 'RuntimeNativeEncryptionInitializationBridge'


def generate(witnesses):
    rows = {(r['domain'], r['branch']): r for r in witnesses['records']}
    assert set(rows) == {(28, False), (28, True), (29, False), (29, True)}
    k = witnesses['coefficient_k']
    imports = [f'RuntimeNativeEncryptionInitialization{d}{b}'
               for d in (28, 29) for b in ('False', 'True')]
    imports += ['RuntimeNativeEncryptionFixed28_Hash', 'RuntimeNativeEncryptionFixed29_Hash',
                'NativeEncryptionFixedKeys']
    body = ''.join(f'import ShielddSecurity.{name}\n' for name in imports)
    body += ('set_option maxHeartbeats 250000\nset_option maxRecDepth 2048\n'
             f'namespace ShielddSecurity.{NAME}\n'
             'variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [Fintype F]\n')
    exports = []
    for domain, lemma in ((28, 'detection_nonzero'), (29, 'payload_nonzero')):
        false, true = rows[domain, False], rows[domain, True]
        u, first, cubic = false['hash'], false['first_x'], false['first_cubic']
        assert (u, first, cubic) == (true['hash'], true['first_x'], true['first_cubic'])
        c1 = witnesses['coefficient_c1']
        body += (f'theorem {lemma} (codec : TransferReduction.CanonicalField F)\n'
                 '    (api : ElligatorNativeRoots.SqrtAPI F) (odd : ringChar F ≠ 2)\n'
                 '    (fiveNonzero : (5 : F) ≠ 0)\n'
                 '    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1) :\n'
                 f'    (NativeEncryptionFixedKeys.fixedValue (d := {CO}.coefficientD) codec api {domain}).x ≠ 0 := by\n'
                 '  unfold NativeEncryptionFixedKeys.fixedValue\n'
                 f'  rw [RuntimeNativeEncryptionFixed{domain}.hash_value]\n'
                 '  dsimp only [ElligatorNativeProgram.generatorValue]\n'
                 f'  rw [RuntimeNativeEncryptionInitialization{domain}False.first_x,\n'
                 f'    RuntimeNativeEncryptionInitialization{domain}False.first_cubic]\n'
                 f'  let chosen := ElligatorNativeRoots.choice api ({cubic} : F)\n'
                 f'  let root := ElligatorNativeRoots.rootValue api\n'
                 f'    (ElligatorNativeRoots.selectedValue api 5 ({u} : F) ({cubic} : F))\n'
                 '  let normalized := ElligatorNativeParity.normalizeRoot codec chosen root\n'
                 '  have square : normalized * normalized =\n'
                 f'      (if chosen then ({cubic} : F) else 5 * ({u} : F) * ({u} : F) * ({cubic} : F)) := by\n'
                 '    rw [ElligatorNativeParity.normalize_square]\n'
                 f'    exact (ElligatorNativeRoots.computed_roots api odd 5 ({u} : F) ({cubic} : F)\n'
                 '      fiveNonzero fiveEuler).2\n'
                 f'  change (GroupNativeCofactor.nativeEight {CO}.coefficientD\n'
                 '    (Elligator.rationalPoint (NativeAssetMap.coefficientK *\n'
                 f'      (if chosen then ({first} : F) else -({first} : F) - NativeAssetMap.coefficientC1))\n'
                 '      (NativeAssetMap.coefficientK * normalized))).x ≠ 0\n'
                 '  cases observed : chosen\n')
        for branch, row in ((False, false), (True, true)):
            body += '  · have selectedSquare : normalized * normalized =\n'
            body += f'        ({row["selected_square"]} : F) := by\n'
            body += '      have computed := square\n'
            body += '      simp only [observed, Bool.false_eq_true, if_false, if_true] at computed\n'
            if branch:
                body += '      exact computed\n'
                selected = f'({first} : F)'
                expression = f'{k} * {first}'
            else:
                body += '      apply computed.trans\n'
                body += checked(f'5 * {u} * {u} * {cubic}', row['selected_square'], '      ')
                selected = f'(-({first} : F) - NativeAssetMap.coefficientC1)'
                expression = f'{k} * (-{first} - {c1})'
            body += f'    have actualS : (NativeAssetMap.coefficientK : F) * {selected} = ({row["s"]} : F) := by\n'
            body += f'      rw [{CO}.k_value' + (']\n' if branch else f', {CO}.c1_value]\n')
            body += checked(expression, row['s'], '      ')
            body += '    simp only [observed, Bool.false_eq_true, if_false, if_true]\n'
            body += f'    rw [actualS, {CO}.k_value]\n'
            body += (f'    exact RuntimeNativeEncryptionInitialization{domain}{"True" if branch else "False"}.nonzero\n'
                     '      normalized selectedSquare\n')
        exports.append(lemma)
    body += ('''theorem fixed_value_nonzero (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (odd : ringChar F ≠ 2)
    (fiveNonzero : (5 : F) ≠ 0)
    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)
    (domain : Nat) (allowed : domain = 28 ∨ domain = 29) :
    (NativeEncryptionFixedKeys.fixedValue (d := CO.coefficientD) codec api domain).x ≠ 0 := by
  rcases allowed with detection | payload
  · subst domain
    exact detection_nonzero codec api odd fiveNonzero fiveEuler
  · subst domain
    exact payload_nonzero codec api odd fiveNonzero fiveEuler

variable {Q Encoded E S R K Signing J : Type} [AddCommGroup J]
  {fr : GroupNativeSdk.FrBytes R} {d : F} {model : Group.StandardCurveModel J d}

/-- Nonidentity of the produced SDK fixed key is a conclusion. The only point
construction is the owned empty-input loaded hash and owned cofactor map;
no chosen subgroup point, root, branch, or output is a premise. -/
theorem sdk_fixed_nonzero
    (hex : ShielddNativeParameterBytes.HexCodec Encoded)
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F)
    (ops : NativeAssetMap.Primitives fq api)
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (points : NativeAssetMap.PointPrimitives fq upstream)
    (imaginary : F) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1)
    (kNonzero : (NativeAssetMap.coefficientK : F) ≠ 0)
    (denominator : Group.NoUnitSquare (-5 : F))
    (edwards : (NativeAssetMap.coefficientK : F) * d = 40960)
    (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)
    (domain : Nat) (allowed : domain = 28 ∨ domain = 29) :
    upstream.embed (upstream.promote
      (NativeEncryptionFixedKeys.fixedGenerator hex fq arithmetic initial square
        api ops upstream points domain)) ≠ 0 := by
  have parameter := CO.d_from_edwards d edwards
  have nonzero : (NativeEncryptionFixedKeys.fixedValue (d := d) codec api domain).x ≠ 0 := by
    rw [parameter]
    exact fixed_value_nonzero codec api odd fiveNonzero fiveEuler domain allowed
  have bounded : domain < 2^64 := by
    rcases allowed with detection | payload <;> subst domain <;> decide
  intro zero
  have coordinates := NativeEncryptionFixedKeys.coordinates hex fq arithmetic initial square
    codec api ops upstream points imaginary nonSquare imaginarySquare kNonzero denominator
    edwards odd fiveNonzero fiveEuler domain bounded
  rw [zero, model.identity] at coordinates
  exact nonzero (congrArg (fun point : Group.Point F => point.x) coordinates.symm)
'''.replace('CO.', CO + '.'))
    exports += ['fixed_value_nonzero', 'sdk_fixed_nonzero']
    return {NAME: finish(body, NAME, exports)}, {NAME: exports}
