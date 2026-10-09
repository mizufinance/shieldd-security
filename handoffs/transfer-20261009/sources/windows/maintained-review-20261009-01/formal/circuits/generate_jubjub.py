"""Emit finite kernel certificates for the actual Jubjub d parameter.

The runtime Scalar/blst prime-field implementation remains an explicit model
boundary. A checked source fingerprint is not a proof of the native field ABI.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
import sys

P = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def parameters(runtime: Path) -> tuple[int, int, dict[str, str]]:
    curve_path = runtime / 'crates/crypto/circuits/src/group.rs'
    field_path = runtime / 'third_party/commonware/cryptography/src/bls12381/primitives/group.rs'
    curve, field = curve_path.read_bytes(), field_path.read_bytes()
    definitions = re.findall(r'pub fn coefficient_d\(\) -> Scalar\s*\{([^{}]*)\}', curve.decode())
    if len(definitions) != 1 or re.sub(r'\s+', '', definitions[0]) != '-Scalar::from(10240)*&Scalar::from(10241).inv()':
        raise ValueError('unsupported runtime coefficient_d definition')
    if ('pub struct Scalar(pub(crate) blst_fr);' not in field.decode()
            or f'r = 0x{P:x}' not in field.decode()):
        raise ValueError('unsupported native scalar field identity')
    d = -10240 * pow(10241, -1, P) % P
    if pow(d, (P - 1) // 2, P) != P - 1:
        raise ValueError('runtime d fails nonsquare certificate')
    imaginary = next((pow(base, (P - 1) // 4, P) for base in range(2, 100)
                      if pow(base, (P - 1) // 2, P) == P - 1), None)
    if imaginary is None or imaginary * imaginary % P != P - 1:
        raise ValueError('no checked square root of minus one')
    return d, imaginary, {'curve': hashlib.sha256(curve).hexdigest(),
                          'field': hashlib.sha256(field).hexdigest()}


def power_steps(base: int, exponent: int) -> list[tuple[int, int, int, int]]:
    """MSB-first certificate; each tuple contains prefix exponent/residue/bit/next."""
    prefix, residue, result = 0, 1, []
    for bit in map(int, bin(exponent)[2:]):
        following = residue * residue * (base if bit else 1) % P
        result.append((prefix, residue, bit, following))
        prefix, residue = prefix * 2 + bit, following
    if prefix != exponent or residue != pow(base, exponent, P):
        raise ValueError('binary power certificate construction failed')
    return result


def validate_steps(base: int, exponent: int, steps: list[tuple[int, int, int, int]]) -> None:
    """Fail closed on altered/truncated traces before rendering the Lean checks."""
    prefix, residue = 0, 1
    if len(steps) != max(1, exponent.bit_length()):
        raise ValueError('power certificate length')
    for previous_exponent, previous_residue, bit, following in steps:
        if (previous_exponent != prefix or previous_residue != residue or bit not in (0, 1)
                or not 0 <= following < P
                or following != residue * residue * (base if bit else 1) % P):
            raise ValueError('invalid modular power step')
        prefix, residue = 2 * prefix + bit, following
    if prefix != exponent:
        raise ValueError('power certificate exponent')


def map_parameters(runtime: Path) -> tuple[dict[str, int], dict[str, str]]:
    """Exact Elligator constants; checks are source binding, not Rust refinement."""
    _, _, hashes = parameters(runtime)
    raw = (runtime / 'crates/crypto/circuits/src/map.rs').read_bytes()
    text = re.sub(r'\s+', '', raw.decode())
    coefficients = ('fncoefficients()->(Scalar,Scalar,Scalar){letk=-Scalar::from(40964);'
                    'letinverse=k.inv();(k,Scalar::from(40962)*&inverse,'
                    'inverse.clone()*&inverse,)}')
    required = (coefficients, 'lettv=z.clone()*u*u;',
                'letx1=-c1.clone()*&(F::one()+&tv).inv();',
                'letgx1=((x1.clone()+c1)*&x1+c2)*&x1;',
                'letx2=-x1.clone()-c1;', 'letgx2=tv*&gx1;',
                'x_coordinates(u,&c1,&c2,&Scalar::from(5))')
    if (any(text.count(anchor) != 1 for anchor in required)
            or text.count('Var::native(Scalar::from(5))') != 2):
        raise ValueError('unsupported Elligator source constants or coordinate equations')
    k = -40964 % P
    c1, c2 = 40962 * pow(k, -1, P) % P, pow(k, -2, P)
    bases = {'z': 5, 'negative_z': -5 % P,
             'discriminant': (c1 * c1 - 4 * c2) % P}
    if any(pow(value, (P - 1) // 2, P) != P - 1 for value in bases.values()):
        raise ValueError('Elligator nonsquare parameter certificate failed')
    return bases, {**hashes, 'map': hashlib.sha256(raw).hexdigest()}


def generate_map(runtime: Path) -> str:
    bases, hashes = map_parameters(runtime)
    half = (P - 1) // 2
    out = [f'''import ShielddSecurity.Jubjub
set_option maxHeartbeats 300000
namespace ShielddSecurity.RuntimeElligatorParameters
-- Exact map/field source identities: {hashes}
-- These finite algebraic certificates do not prove the native field ABI or
-- source-to-circuit correspondence. Cardinality is essential for nonsquares.
def modulus : Nat := {P}
variable {{F : Type}} [Field F] [CharP F modulus]
theorem minus_one_residue : (({P-1} : Int) : F) = -1 := by
  have result := Compiler.coefficient_mod (F := F) (p := modulus) (-1)
  have checked : (-1 : Int) % (modulus : Int) = {P-1} := by decide
  rw [checked] at result
  simpa using result
theorem two_nonzero : (2 : F) ≠ 0 := by
  intro zero
  have impossible : (2 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
''']
    for name, base in bases.items():
        steps = power_steps(base, half)
        validate_steps(base, half, steps)
        out.append(f'def {name} : Int := {base}\n'
                   f'theorem {name}_power_0 : ({name} : F) ^ 0 = ((1 : Int) : F) := by simp\n')
        for index, (prefix, residue, bit, following) in enumerate(steps, 1):
            lemma = 'power_square_multiply' if bit else 'power_square'
            out.append(f'''theorem {name}_power_{index} : ({name} : F) ^ {prefix*2+bit} = (({following} : Int) : F) := by
  exact Jubjub.{lemma} (p := modulus) {name} {residue} {following} {prefix}
    {name}_power_{index-1} (by decide)
''')
        out.append(f'''theorem {name}_euler : ({name} : F) ^ {half} = -1 :=
  ({name}_power_{len(steps)} (F := F)).trans minus_one_residue
theorem {name}_nonsquare [Fintype F] (cardinality : Fintype.card F = modulus) :
    Group.NoUnitSquare ({name} : F) := by
  exact Jubjub.nonsquare_of_euler cardinality (half := {half}) (by decide)
    two_nonzero {name} {name}_euler
set_option pp.all true in
#check @{name}_euler
set_option pp.all true in
#check @{name}_nonsquare
#print axioms {name}_euler
#print axioms {name}_nonsquare
''')
    out.append('end ShielddSecurity.RuntimeElligatorParameters\n')
    return ''.join(out)


def generate_map_algebra(runtime: Path) -> str:
    """Small exact parameter joins; keeps the accepted Euler module unchanged."""
    bases, hashes = map_parameters(runtime)
    d, _, _ = parameters(runtime)
    k, j = P - 40964, 40962
    c1, c2 = j * pow(k, -1, P) % P, pow(k, -2, P)
    square = c1 * c1 % P
    kk = k * k % P
    assert k * c1 % P == j and kk * c2 % P == 1
    assert k * d % P == j - 2
    assert (square - 4 * c2) % P == bases['discriminant']
    out = [f'''import ShielddSecurity.RuntimeElligatorParameters
import ShielddSecurity.RuntimeJubjub
import ShielddSecurity.ElligatorChoice
namespace ShielddSecurity.RuntimeElligatorAlgebra
set_option maxHeartbeats 300000
-- Exact source identities: {hashes}; native ABI/source correspondence is separate.
def modulus : Nat := {P}
def k : Int := {k}
def j : Int := {j}
def c1 : Int := {c1}
def c2 : Int := {c2}
variable {{F : Type}} [Field F] [CharP F modulus]

private theorem nonzero_residue (value : Nat) (positive : 0 < value)
    (bound : value < modulus) : (value : F) ≠ 0 := by
  intro zero
  have impossible := bounded_cast_injective (F := F) (p := modulus)
    bound (show 0 < modulus by decide) (by simpa using zero)
  omega

theorem k_nonzero : (k : F) ≠ 0 := by
  simpa only [k, Int.cast_ofNat] using nonzero_residue (F := F) {k} (by decide) (by decide)
theorem c1_nonzero : (c1 : F) ≠ 0 := by
  simpa only [c1, Int.cast_ofNat] using nonzero_residue (F := F) {c1} (by decide) (by decide)
theorem discriminant_nonzero : (RuntimeElligatorParameters.discriminant : F) ≠ 0 := by
  simpa only [RuntimeElligatorParameters.discriminant, Int.cast_ofNat] using
    nonzero_residue (F := F) {bases['discriminant']} (by decide) (by decide)

theorem scale : (k : F) = -((j : F) + 2) := by
  have reduced := Compiler.coefficient_mod (F := F) (p := modulus) (-40964)
  have checked : (-40964 : Int) % (modulus : Int) = k := by decide
  rw [checked] at reduced
  have integer : (-40964 : Int) = -(j + 2) := by decide
  rw [integer, Int.cast_neg, Int.cast_add, Int.cast_ofNat] at reduced
  exact reduced

theorem first : (k : F) * (c1 : F) = (j : F) := by
  exact Jubjub.product_certificate (F := F) (p := modulus) k c1 j (by decide)
theorem second : (k : F) * (k : F) * (c2 : F) = 1 := by
  have square := Jubjub.product_certificate (F := F) (p := modulus) k k {kk} (by decide)
  rw [square]
  simpa only [Int.cast_one] using
    Jubjub.product_certificate (F := F) (p := modulus) {kk} c2 1 (by decide)
theorem edwards : (k : F) * (RuntimeJubjub.d : F) = (j : F) - 2 := by
  have product := Jubjub.product_certificate (F := F) (p := modulus) k RuntimeJubjub.d {j-2} (by decide)
  change (k : F) * (RuntimeJubjub.d : F) = ((j - 2 : Int) : F) at product
  have difference : ((j - 2 : Int) : F) = (j : F) - 2 := by
    simp only [Int.cast_sub, Int.cast_ofNat]
  exact product.trans difference

theorem discriminant_match : (c1 : F) * (c1 : F) - 4 * (c2 : F) =
    (RuntimeElligatorParameters.discriminant : F) := by
  have square := Jubjub.product_certificate (F := F) (p := modulus) c1 c1 {square} (by decide)
  have reduced := Compiler.coefficient_mod (F := F) (p := modulus) ({square} - 4 * c2)
  have checked : ({square} - 4 * c2 : Int) % (modulus : Int) = RuntimeElligatorParameters.discriminant := by decide
  rw [checked] at reduced
  rw [square]
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using reduced.symm

theorem first_cubic_nonzero [Fintype F] (cardinality : Fintype.card F = modulus)
    (x tv : F) (coordinate : (1 + tv) * x = -(c1 : F)) :
    Elligator.cubic (c1 : F) (c2 : F) x ≠ 0 := by
  apply ElligatorChoice.first_cubic_nonzero (c1 : F) (c2 : F) x tv c1_nonzero coordinate
  · rw [discriminant_match]; exact discriminant_nonzero
  · rw [discriminant_match]; exact RuntimeElligatorParameters.discriminant_nonsquare cardinality

variable [DecidableEq F]
theorem selected_root_on_curve (x y : F) (root : y * y = Elligator.cubic (c1 : F) (c2 : F) x) :
    Group.OnCurve (RuntimeJubjub.d : F) (Elligator.rationalPoint ((k : F) * x) ((k : F) * y)) := by
  exact ElligatorCurve.rational_on_curve (k : F) (j : F) (RuntimeJubjub.d : F) _ _ k_nonzero scale edwards
    (ElligatorCurve.scaled_cubic (k : F) (j : F) (c1 : F) (c2 : F) x y first second root)
''']
    names = ['k_nonzero', 'c1_nonzero', 'discriminant_nonzero', 'scale', 'first',
             'second', 'edwards', 'discriminant_match', 'first_cubic_nonzero', 'selected_root_on_curve']
    for name in names:
        out.append(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n')
    out.append('end ShielddSecurity.RuntimeElligatorAlgebra\n')
    return ''.join(out)


def generate_map_image(runtime: Path) -> str:
    """Join total inverse rows to curve/cofactor facts without witness-membership premises."""
    _, hashes = map_parameters(runtime)
    out = [f'''import ShielddSecurity.RuntimeElligatorAlgebra
import ShielddSecurity.TransferSubgroup
namespace ShielddSecurity.RuntimeElligatorImage
set_option maxHeartbeats 300000
-- Exact map identities: {hashes}; captured row/source/native correspondence is separate.
variable {{F : Type}} [Field F] [CharP F RuntimeElligatorAlgebra.modulus] [DecidableEq F]
open RuntimeElligatorAlgebra

def image (x y inverse zero : F) : Group.Point F :=
  ⟨inverse * ((k : F) * x + 1) * ((k : F) * x),
   inverse * ((k : F) * y) * ((k : F) * x - 1) + zero⟩

theorem image_on_curve (x y inverse zero : F)
    (root : y * y = Elligator.cubic (c1 : F) (c2 : F) x)
    (product : (((k : F) * x + 1) * ((k : F) * y)) * inverse = 1 - zero)
    (annihilate : (((k : F) * x + 1) * ((k : F) * y)) * zero = 0)
    (inverseZero : inverse * zero = 0) : Group.OnCurve (RuntimeJubjub.d : F) (image x y inverse zero) := by
  have equal : image x y inverse zero = Elligator.rationalPoint ((k : F) * x) ((k : F) * y) :=
    Elligator.rational_point_sound _ _ inverse zero product annihilate inverseZero
  rw [equal]
  exact selected_root_on_curve x y root

theorem cofactor_image {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J (RuntimeJubjub.d : F)) (order : Nat)
    (standardOrder : ∀ point : J, (8 * order) • point = 0)
    (x y inverse zero : F) (twice four eight : Group.Point F)
    (root : y * y = Elligator.cubic (c1 : F) (c2 : F) x)
    (product : (((k : F) * x + 1) * ((k : F) * y)) * inverse = 1 - zero)
    (annihilate : (((k : F) * x + 1) * ((k : F) * y)) * zero = 0)
    (inverseZero : inverse * zero = 0)
    (first : twice = Group.affineAdd (RuntimeJubjub.d : F) (image x y inverse zero) (image x y inverse zero))
    (second : four = Group.affineAdd (RuntimeJubjub.d : F) twice twice)
    (third : eight = Group.affineAdd (RuntimeJubjub.d : F) four four) :
    ∃ represented : J, model.coordinates represented = eight ∧ order • represented = 0 := by
  exact Group.cofactor_image_annihilated (RuntimeJubjub.d : F) model order standardOrder
    (image x y inverse zero) twice four eight
    (image_on_curve x y inverse zero root product annihilate inverseZero) first second third

theorem cofactor_nonidentity {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J (RuntimeJubjub.d : F)) (order : Nat)
    (standardOrder : ∀ point : J, (8 * order) • point = 0)
    (x y inverse zero : F) (twice four eight : Group.Point F)
    (root : y * y = Elligator.cubic (c1 : F) (c2 : F) x)
    (product : (((k : F) * x + 1) * ((k : F) * y)) * inverse = 1 - zero)
    (annihilate : (((k : F) * x + 1) * ((k : F) * y)) * zero = 0)
    (inverseZero : inverse * zero = 0)
    (first : twice = Group.affineAdd (RuntimeJubjub.d : F) (image x y inverse zero) (image x y inverse zero))
    (second : four = Group.affineAdd (RuntimeJubjub.d : F) twice twice)
    (third : eight = Group.affineAdd (RuntimeJubjub.d : F) four four)
    (xInverse : F) (nonidentity : xInverse * eight.x = 1) :
    ∃ represented : J, model.coordinates represented = eight ∧ order • represented = 0 ∧ represented ≠ 0 := by
  exact TransferSubgroup.cofactor_nonidentity (RuntimeJubjub.d : F) model order standardOrder
    (image x y inverse zero) twice four eight eight
    (image_on_curve x y inverse zero root product annihilate inverseZero)
    first second third rfl xInverse nonidentity
''']
    for name in ['image_on_curve', 'cofactor_image', 'cofactor_nonidentity']:
        out.append(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n')
    out.append('end ShielddSecurity.RuntimeElligatorImage\n')
    return ''.join(out)


def generate(runtime: Path) -> str:
    d, imaginary, hashes = parameters(runtime)
    half = (P - 1) // 2
    out = [f'''import ShielddSecurity.Jubjub
set_option maxHeartbeats 300000
namespace ShielddSecurity.RuntimeJubjub
-- Runtime curve source SHA256: {hashes['curve']}
-- Native field source SHA256: {hashes['field']}
-- Source extraction and native prime-field/cardinality correspondence remain
-- explicit boundaries. No theorem asserts this for extension fields.
def modulus : Nat := {P}
def d : Int := {d}
def imaginary : Int := {imaginary}
variable {{F : Type}} [Field F] [CharP F modulus]

theorem power_0 : (d : F) ^ 0 = ((1 : Int) : F) := by simp
''']
    steps = power_steps(d, half)
    validate_steps(d, half, steps)
    for index, (prefix, residue, bit, following) in enumerate(steps, 1):
        lemma = 'power_square_multiply' if bit else 'power_square'
        out.append(f'''theorem power_{index} : (d : F) ^ {prefix * 2 + bit} = (({following} : Int) : F) := by
  exact Jubjub.{lemma} (p := modulus) d {residue} {following} {prefix}
    power_{index - 1} (by decide)
''')
    out.append(f'''
theorem minus_one_residue : (({P - 1} : Int) : F) = -1 := by
  have checked : (-1 : Int) % (modulus : Int) = {P - 1} := by decide
  have result := Compiler.coefficient_mod (F := F) (p := modulus) (-1)
  rw [checked] at result
  simpa using result

theorem euler : (d : F) ^ {half} = -1 :=
  (power_{len(steps)} (F := F)).trans minus_one_residue

theorem imaginary_square : (imaginary : F) * (imaginary : F) = -1 := by
  exact (Jubjub.product_certificate (F := F) (p := modulus)
    imaginary imaginary {P - 1} (by decide)).trans minus_one_residue

theorem runtime_coefficient : (d : F) = -(10240 : F) / 10241 := by
  have denominator : (10241 : F) ≠ 0 := by
    intro zero
    have impossible : (10241 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
  apply (eq_div_iff denominator).2
  have product := Jubjub.product_certificate (F := F) (p := modulus)
    d 10241 {P - 10240} (by decide)
  have negative := Compiler.coefficient_mod (F := F) (p := modulus) (-10240)
  have checked : (-10240 : Int) % (modulus : Int) = {P - 10240} := by decide
  rw [checked] at negative
  simpa using product.trans (by simpa using negative)

theorem nonsquare [Fintype F] (cardinality : Fintype.card F = modulus) :
    Group.NoUnitSquare (d : F) := by
  have two : (2 : F) ≠ 0 := by
    intro zero
    have impossible : (2 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
  exact Jubjub.nonsquare_of_euler cardinality (half := {half}) (by decide) two d euler

set_option pp.all true in
#check @euler
#print axioms euler
set_option pp.all true in
#check @imaginary_square
#print axioms imaginary_square
set_option pp.all true in
#check @runtime_coefficient
#print axioms runtime_coefficient
set_option pp.all true in
#check @nonsquare
#print axioms nonsquare
end ShielddSecurity.RuntimeJubjub
''')
    return ''.join(out)


if __name__ == '__main__':
    runtime, output = map(Path, sys.argv[1:])
    temporary = output.with_suffix(output.suffix + '.tmp')
    temporary.write_text(generate(runtime), encoding='utf-8', newline='\n')
    temporary.replace(output)
