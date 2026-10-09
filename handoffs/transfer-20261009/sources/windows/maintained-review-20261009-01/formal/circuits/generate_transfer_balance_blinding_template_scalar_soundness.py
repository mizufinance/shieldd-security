"""Genuine H fixed-window scalar composition on the same assignment.

Own H ingress validates all captured rows and allocation/source roles. Shared
algebraic patterns derive endpoints; native SDK correspondence remains separate.
"""
from . import transfer_balance_blinding_program as whole
from . import transfer_fixed_spend as fixed, transfer_relation as relation
from .generate_hash_round import _signature_audits, signed
from .transfer_balance_rows import source_index


def generate(parent, pages, expected_base, expected_blinding, extracted, *, readonly_lcs=()):
    accepted = whole.plan(parent, pages, expected_base, expected_blinding, extracted, readonly_lcs)
    chunks = accepted['checked']['chunks']
    if (len(chunks) != 8 or
            [c['metadata']['window_start'] for c in chunks] != list(range(0,126,16)) or
            len(accepted['loop']['programs']) != 126):
        raise relation.RelationError('VALUE_BLINDING exact eight-page126 scalar inventory')
    d = signed(fixed.D)
    trace = f'RuntimeBalanceBlindingTemplateOrdinaryTrace'
    scalar = f'RuntimeBalanceBlindingTemplateScalarTrace'
    sound = f'RuntimeBalanceBlindingTemplateOrdinarySoundness'
    first = f'RuntimeBalanceBlindingWindow000'
    ns = f'RuntimeBalanceBlindingTemplateScalarSoundness'
    low = '(encodeBits 252 n)[0]?.getD false'
    high = '(encodeBits 252 n)[1]?.getD false'
    source = f'''import ShielddSecurity.{scalar}
import ShielddSecurity.{sound}
import ShielddSecurity.{first}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 200000

def rows (n : Nat) : List Row := {first}.rawRows ++ GroupFixedCircuitCompletion.rows
  (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)

theorem actual_native_sound {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (bound : n < 2 ^ 252)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (baseMeaning : ({first}.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho (rows n))
    (lowValue : eval rho {first}.low = if {low} then 1 else 0)
    (highValue : eval rho {first}.high = if {high} then 1 else 0)
    (bits : ∀ window ∈ {trace}.windows n,
      eval rho window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval rho window.program.high = (if window.program.highBit then 1 else 0)) :
    GroupFixedCircuitCompletion.point rho
      (GroupFixedTemplateTrace.endpoint {trace}.input ({trace}.windows n)) =
      model.coordinates (n • generator) := by
  have initialRows : Satisfies rho {first}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have ordinaryRows : Satisfies rho (GroupFixedCircuitCompletion.rows
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)) := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have inputZero : {first}.input rho = model.coordinates 0 := by
    rw [model.identity]
    simp [{first}.input,Group.identityPoint,eval,one]
  have initial := {first}.actual_window_coordinates rho one imaginary model nonSquare
    imaginarySquare 0 generator inputZero baseMeaning initialRows
  have decoded (lc : Linear) (bit : Bool) (meaning : eval rho lc = if bit then 1 else 0) :
      ScalarBits.decodeBit rho lc = bit := by
    cases bit <;> simp [ScalarBits.decodeBit,meaning]
  have lowDecoded := decoded {first}.low ({low}) lowValue
  have highDecoded := decoded {first}.high ({high}) highValue
  have digitSame : GroupFixedWindows.fixedDigit ({first}.window rho) =
      GroupFixedWindows.fixedDigit ({scalar}.firstWitness (F := F) n) := by
    simp only [{first}.window,{scalar}.firstWitness,GroupFixedWindows.fixedDigit,
      lowDecoded,highDecoded]
  have inputMeaning : GroupFixedCircuitCompletion.point rho {trace}.input =
      model.coordinates (GroupFixedWindows.fixedDigit ({scalar}.firstWitness (F := F) n) • generator) := by
    change {first}.output rho = _
    simpa only [zero_add,digitSame] using initial.1
  have nextMeaning : GroupFixedWindowTemplate.castPoint {trace}.base =
      model.coordinates (4 • generator) := by
    change ({first}.nextBase : Group.Point F) = _
    exact initial.2
  have ordinary := {sound}.actual_native_sound model rho n
    (GroupFixedWindows.fixedDigit ({scalar}.firstWitness (F := F) n) • generator)
    (4 • generator) one four imaginary nonSquare imaginarySquare inputMeaning nextMeaning ordinaryRows bits
  have scalarValue := GroupFixedTemplateScalarDigits.folded_tail_value
    ({scalar}.firstWitness (F := F) n) (({trace}.windows n).map (fun window => window.witness rho))
    generator 252 n ({scalar}.actual_word rho n) bound
  exact ordinary.trans (congrArg model.coordinates scalarValue)

#print axioms actual_native_sound
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
