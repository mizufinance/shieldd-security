"""Finite certificates for the owned Elligator constant 5 in the circuit field."""
from .generate_hash_round import _signature_audits

MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def witness():
    exponent = MODULUS // 2
    bits = [digit == '1' for digit in bin(exponent)[2:]]
    exponents, values = [0], [1]
    for bit in bits:
        exponents.append(exponents[-1] * 2 + int(bit))
        values.append((values[-1] ** 2 * (5 if bit else 1)) % MODULUS)
    assert len(bits) == 254 and exponents[-1] == exponent and values[-1] == MODULUS - 1
    return dict(bits=bits, exponents=exponents, values=values)


def validate(data):
    bits, exponents, values = data['bits'], data['exponents'], data['values']
    assert len(bits) == 254 and len(exponents) == len(values) == 255
    assert all(type(bit) is bool for bit in bits)
    assert exponents[0] == 0 and values[0] == 1
    assert all(type(value) is int and 0 <= value < MODULUS for value in values)
    for index, bit in enumerate(bits):
        assert exponents[index + 1] == exponents[index] * 2 + int(bit)
        assert values[index + 1] == (values[index] ** 2 * (5 if bit else 1)) % MODULUS
    assert exponents[-1] == MODULUS // 2 and values[-1] == MODULUS - 1


def generate(data=None):
    data = witness() if data is None else data
    validate(data)
    base = 'RuntimeNativeEncryptionFieldFacts'
    name = base + '_Data'
    bits = ', '.join('true' if bit else 'false' for bit in data['bits'])
    exponents = ', '.join(map(str, data['exponents']))
    values = ', '.join(map(str, data['values']))
    text = f'''import ShielddSecurity.NativeEncryptionFieldArithmetic

namespace ShielddSecurity.{name}
set_option maxHeartbeats 250000
set_option maxRecDepth 2048

def bits (index : Nat) : Bool := ([{bits}] : List Bool).getD index false
def exponents (index : Nat) : Nat := ([{exponents}] : List Nat).getD index 0
def values (index : Nat) : Int := ([{values}] : List Int).getD index 0

theorem initial : exponents 0 = 0 ∧ values 0 = 1 := by decide
theorem last_exponent : exponents 254 = Scalar.modulus / 2 := by decide
theorem last_value : values 254 = (Scalar.modulus : Int) - 1 := by decide
#print axioms initial
#print axioms last_exponent
#print axioms last_value
end ShielddSecurity.{name}
'''
    modules = [(name, _signature_audits(text))]
    for block in range(32):
        name = base + f'_Steps{block:02d}'
        start, stop = 8 * block, min(8 * (block + 1), 254)
        text = f'''import ShielddSecurity.{base}_Data

namespace ShielddSecurity.{name}
open {base}_Data
set_option maxHeartbeats 250000
set_option maxRecDepth 2048

'''
        for index in range(start, stop):
            text += f'''theorem integer{index:03d} :
    values {index + 1} % (Scalar.modulus : Int) =
      (values {index} ^ 2 * (if bits {index} then 5 else 1)) % (Scalar.modulus : Int) := by decide
theorem exponent{index:03d} :
    exponents {index + 1} = exponents {index} * 2 + (if bits {index} then 1 else 0) := by decide
#print axioms integer{index:03d}
#print axioms exponent{index:03d}
'''
        for kind, conclusion in (
            ('integer', '(values (index + 1) % (Scalar.modulus : Int)) =\n'
             '      (values index ^ 2 * (if bits index then 5 else 1)) % (Scalar.modulus : Int)'),
            ('exponent', 'exponents (index + 1) = exponents index * 2 + (if bits index then 1 else 0)')):
            choices = '\n'.join(f'    | exact {kind}{index:03d}' for index in range(start, stop))
            text += f'''theorem {kind}_steps (index : Nat) (lower : {start} ≤ index) (upper : index < {stop}) :
    {conclusion} := by
  interval_cases index <;> first
{choices}
#print axioms {kind}_steps
'''
        text += f'end ShielddSecurity.{name}\n'
        modules.append((name, _signature_audits(text)))
    name = base
    text = ''.join(f'import ShielddSecurity.{base}_Steps{block:02d}\n' for block in range(32))
    text += f'''
namespace ShielddSecurity.{name}
open {base}_Data
set_option maxHeartbeats 500000
set_option maxRecDepth 2048

'''
    for kind, conclusion in (
        ('integer', 'values (index + 1) % (Scalar.modulus : Int) =\n'
         '      (values index ^ 2 * (if bits index then 5 else 1)) % (Scalar.modulus : Int)'),
        ('exponent', 'exponents (index + 1) = exponents index * 2 + (if bits index then 1 else 0)')):
        choices = '\n'.join(f'    | exact {base}_Steps{block:02d}.{kind}_steps index (by omega) (by omega)'
            for block in range(32))
        text += f'''theorem {kind}_steps (index : Nat) (bounded : index < 254) :
    {conclusion} := by
  have quotient : index / 8 < 32 := by omega
  generalize division : index / 8 = block at quotient
  interval_cases block <;> first
{choices}
#print axioms {kind}_steps
'''
    text += '''theorem five_euler {F : Type} [Field F] [CharP F Scalar.modulus] [Fintype F]
    (codec : TransferReduction.CanonicalField F) :
    (5 : F) ^ (Fintype.card F / 2) = -1 := by
  apply NativeEncryptionFieldArithmetic.euler_from_trace codec 254 bits exponents values
  · exact initial.1
  · simpa only [initial.2, Int.cast_one]
  · exact exponent_steps
  · intro index bounded
    exact NativeEncryptionFieldArithmetic.integer_step
      (values index) (values (index + 1)) (bits index) (integer_steps index bounded)
  · exact last_exponent
  · exact last_value

theorem initialization_prerequisites {F : Type} [Field F] [CharP F Scalar.modulus] [Fintype F]
    (codec : TransferReduction.CanonicalField F) :
    ringChar F ≠ 2 ∧ (5 : F) ≠ 0 ∧ (5 : F) ^ (Fintype.card F / 2) = -1 :=
  ⟨NativeEncryptionFieldArithmetic.odd_characteristic,
    NativeEncryptionFieldArithmetic.five_nonzero, five_euler codec⟩
#print axioms five_euler
#print axioms initialization_prerequisites
'''
    text += f'end ShielddSecurity.{name}\n'
    modules.append((name, _signature_audits(text)))
    return modules, data
