"""Finite literal coordinates from owned hashes, branch admission and parity.

Two fixed instances use small polynomial certificates and three doubles. The
false branch transfers the existing -5 nonsquare proof through a scaled square;
no additional wide exponent trace or requested native root is introduced.
"""
from .transfer_relation import MODULUS,RelationError
from .generate_hash_round import _signature_audits

CASTS = 'Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero'


def _fact(expression,expected,indent='  '):
    return (indent+'have checked := NativeEncryptionInitializationSquares.polynomial_certificate (F := F)\n'+
        indent+f'  ({expression} : Int) {expected} (by decide)\n'+
        indent+f'simpa only [{CASTS}] using checked\n')


def generate(records,nonsquare_factor):
    p = MODULUS
    if (not isinstance(records,list) or len(records) != 2 or
            [r.get('domain') for r in records] != [28,29] or
            type(nonsquare_factor) is not int or not 0 < nonsquare_factor < p):
        raise RelationError('fixed literal exact two domains and bounded nonsquare factor required')
    k = (-40964)%p
    c1 = 40962*pow(k,-1,p)%p
    c2 = pow(k,-1,p)**2%p
    d = -10240*pow(10241,-1,p)%p
    modules = []
    for r in records:
        domain = r['domain']
        branch = domain == 29
        fields = ('hash','first_x','first_cubic','selected_x','selected_square','normalized_root','rational_inverse')
        if any(type(r.get(n)) is not int or not 0 <= r[n] < p for n in fields):
            raise RelationError('fixed literal canonical arithmetic values required')
        u,x1,first,selected,square,root,rinv = [r[n] for n in fields]
        if (r.get('arity') != 0 or r.get('choice') is not branch or
                u != {28:25393117207726835668365714691712723504007270369233823238690202386849480471793,
                      29:47127370616510101739034211210395480563266834468464461032177054264535895577291}[domain] or
                x1 != -c1*pow((1+5*u*u)%p,-1,p)%p or first != ((x1+c1)*x1+c2)*x1%p or
                first == 0 or selected != (x1 if branch else (-x1-c1)%p) or
                square != (first if branch else 5*u*u*first%p) or
                root*root%p != square or root%2 != int(branch)):
            raise RelationError('fixed literal first/selected/normalized arithmetic mismatch')
        if not branch and (-5*nonsquare_factor*nonsquare_factor)%p != first:
            raise RelationError('fixed literal intended scaled nonsquare arithmetic mismatch')
        s,t = selected*k%p,root*k%p
        denominator = (s+1)*t%p
        if denominator*rinv%p != 1:
            raise RelationError('fixed literal rational inverse arithmetic mismatch')
        initial = (rinv*(s+1)*s%p,rinv*t*(s-1)%p)
        doubles = r.get('doubles')
        if not isinstance(doubles,list) or len(doubles) != 3:
            raise RelationError('fixed literal three doubles required')
        current = initial
        for index,step in enumerate(doubles):
            if step.get('step') != index or tuple(step.get('input',())) != current:
                raise RelationError('fixed literal actual doubling chain mismatch')
            x,y = current
            delta = d*x*x*y*y%p
            inv = step.get('inverse')
            if (type(inv) is not int or not 0 < inv < p or step.get('delta') != delta or
                    step.get('denominator') != (1+delta)*(1-delta)%p or
                    (1+delta)*(1-delta)*inv%p != 1):
                raise RelationError('fixed literal intended doubling inverse arithmetic mismatch')
            result = (2*x*y*(1-delta)*inv%p,(y*y+x*x)*(1+delta)*inv%p)
            if tuple(step.get('output',())) != result:
                raise RelationError('fixed literal intended doubling output arithmetic mismatch')
            current = result
        if tuple(r.get('point',())) != current:
            raise RelationError('fixed literal final point arithmetic mismatch')
        base = f'RuntimeNativeEncryptionInitialization{domain}'+('True' if branch else 'False')
        name = f'RuntimeNativeEncryptionFixed{domain}Literal'
        choice = 'true' if branch else 'false'
        coeff = 'RuntimeNativeEncryptionInitializationCoefficients'
        model = 'NativeEncryptionInitializationLiteral'
        source = f'''import ShielddSecurity.NativeEncryptionInitializationLiteral
import ShielddSecurity.{base}
import ShielddSecurity.RuntimeNativeEncryptionFixed{domain}_Hash
namespace ShielddSecurity.{name}
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
variable {{F : Type}} [Field F] [DecidableEq F] [CharP F Scalar.modulus] [Fintype F]
private theorem first_nonzero : ({first} : F) ≠ 0 :=
  NativeEncryptionFixedArithmetic.cast_nonzero {first} (by decide) (by decide)
theorem choice_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) : ElligatorNativeRoots.choice api ({first} : F) = {choice} := by
'''
        if branch:
            source += f'  apply {model}.choice_true api ({first} : F) ({root} : F)\n'
            source += _fact(f'{root} * {root}',first)
        else:
            source += f'''  apply {model}.choice_false api ({first} : F)
  apply {model}.scaled_nonsquare (-5 : F) ({first} : F) ({nonsquare_factor} : F)
    (NativeEncryptionInitializationComplete.denominator codec) first_nonzero
'''
            source += _fact(f'-5 * {nonsquare_factor} * {nonsquare_factor}',first)
        source += f'''theorem normalized_root (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) :
    ElligatorNativeParity.normalizeRoot codec {choice}
      (ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.selectedValue api 5
        ({u} : F) ({first} : F))) = ({root} : F) := by
  have prerequisites := RuntimeNativeEncryptionFieldFacts.initialization_prerequisites codec
  have square : ({root} : F) * {root} = if {choice} then ({first} : F) else 5 * {u} * {u} * {first} := by
    simp only [Bool.false_eq_true, if_false, if_true]
'''
        # The RHS is a polynomial expression rather than a normalized numeral;
        # independently certify its residue and the candidate's square.
        target_expr = str(first) if branch else f'5 * {u} * {u} * {first}'
        if not branch:
            source += f'    have right : ({target_expr} : F) = ({square} : F) := by\n'+_fact(target_expr,square,'      ')
            source += '    rw [right]\n'
        source += _fact(f'{root} * {root}',square,'    ')
        source += f'''  have parity : codec.decode ({root} : F) % 2 = if {choice} then 1 else 0 := by
    rw [TransferReduction.decode_canonical_cast codec {root} (by decide)]
    decide
  have result := {model}.normalized_literal codec api prerequisites.1 prerequisites.2.1 prerequisites.2.2
    ({u} : F) ({first} : F) ({root} : F) {choice} first_nonzero (choice_value codec api) square parity
  simpa only [choice_value codec api] using result
private theorem scaled_x : ({k} : F) * ({str(x1) if branch else f'-{x1} - {c1}'} : F) = ({s} : F) := by
'''+_fact(f'{k} * ({str(x1) if branch else f"-{x1} - {c1}"})',s)
        source += f'private theorem scaled_root : ({k} : F) * {root} = ({t} : F) := by\n'+_fact(f'{k} * {root}',t)
        source += f'''theorem rational_point : Elligator.rationalPoint ({s} : F) ({t} : F) = ⟨{initial[0]},{initial[1]}⟩ := by
  apply {model}.rational_literal ({s} : F) ({t} : F) ({rinv} : F)
'''
        for expression,value in ((f'(({s}+1)*{t})*{rinv}',1),
                                 (f'{rinv}*({s}+1)*{s}',initial[0]),
                                 (f'{rinv}*{t}*({s}-1)',initial[1])):
            source += '  ·\n'+_fact(expression,value,'    ')
        for index,step in enumerate(doubles):
            x,y = step['input'];ox,oy = step['output'];delta=step['delta'];inv=step['inverse']
            source += f'''theorem double{index} : GroupFixedWindows.nativeAdd ({coeff}.coefficientD : F)
    (⟨{x},{y}⟩ : Group.Point F) ⟨{x},{y}⟩ = ⟨{ox},{oy}⟩ := by
  have delta_value : Group.delta ({coeff}.coefficientD : F)
      (⟨{x},{y}⟩ : Group.Point F) ⟨{x},{y}⟩ = ({delta} : F) := by
    rw [Group.delta, {coeff}.d_value]
'''+_fact(f'{d}*{x}*{x}*{y}*{y}',delta,'    ')
            source += f'  apply {model}.double_literal ({coeff}.coefficientD : F) (⟨{x},{y}⟩ : Group.Point F) ({inv} : F)\n'
            for expression,value,defs in ((f'((1+{delta})*(1-{delta}))*{inv}',1,''),
                    (f'({x}*{y}+{y}*{x})*(1-{delta})*{inv}',ox,'Group.cross, '),
                    (f'({y}*{y}+{x}*{x})*(1+{delta})*{inv}',oy,'Group.diagonal, ')):
                source += f'  · simp only [{defs}delta_value]\n'+_fact(expression,value,'    ')
        source += f'''theorem fixed_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) :
    NativeEncryptionFixedKeys.fixedValue (d := {coeff}.coefficientD) codec api {domain} =
      (⟨{current[0]},{current[1]}⟩ : Group.Point F) := by
  rw [NativeEncryptionFixedKeys.fixedValue, RuntimeNativeEncryptionFixed{domain}.hash_value]
  simp only [ElligatorNativeProgram.generatorValue, {base}.first_x, {base}.first_cubic,
    choice_value codec api, Bool.false_eq_true, if_false, if_true]
  rw [normalized_root codec api]
  simp only [{coeff}.k_value, {coeff}.c1_value, scaled_x, scaled_root, rational_point]
  simp only [GroupNativeCofactor.nativeEight, double0, double1, double2]
'''
        for theorem in ('choice_value','normalized_root','rational_point','double0','double1','double2','fixed_value'):
            source += '#print axioms '+theorem+'\n'
        modules.append((name,_signature_audits(source+f'end ShielddSecurity.{name}\n')))
    return modules
