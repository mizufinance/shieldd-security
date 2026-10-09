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
    copy = accepted['bounds']['constant_copy']
    d = signed(fixed.D)
    trace = f'RuntimeBalanceBlindingTemplateOrdinaryTrace'
    ns = f'RuntimeBalanceBlindingTemplateScalarTrace'
    low = '(encodeBits 252 n)[0]?.getD false'
    high = '(encodeBits 252 n)[1]?.getD false'
    source = f'''import ShielddSecurity.{trace}
import ShielddSecurity.GroupFixedTemplateEncodedWord
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def firstWitness {{F : Type}} [Field F] (n : Nat) : GroupFixedWindows.FixedWindowWitness F :=
  ⟨{low},{high},Group.identityPoint,Group.identityPoint,Group.identityPoint,Group.identityPoint⟩

theorem actual_word {{F : Type}} [Field F] (rho : Nat → F) (n : Nat) :
    GroupFixedChunks.windowBits (firstWitness n ::
      (({trace}.windows n).map (fun window => window.witness rho))) = encodeBits 252 n := by
  calc
    _ = (List.range 252).map (fun index => (encodeBits 252 n)[index]?.getD false) := by rfl
    _ = encodeBits 252 n := GroupFixedTemplateEncodedWord.encoded_word 252 n

theorem actual_native_scalar_complete {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (bound : n < 2 ^ 252)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho {trace}.input =
      model.coordinates (GroupFixedWindows.fixedDigit (firstWitness (F := F) n) • generator))
    (baseMeaning : GroupFixedWindowTemplate.castPoint {trace}.base = model.coordinates (4 • generator))
    (bits : ∀ program ∈ ({trace}.windows n).map GroupFixedTemplateTrace.Window.program,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    let completed := GroupFixedCircuitCompletion.run rho
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)
    Satisfies completed (GroupFixedCircuitCompletion.rows
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)) ∧
    (∀ column ∈ {trace}.kept, completed column = rho column) ∧
    GroupFixedCircuitCompletion.point completed
      (GroupFixedTemplateTrace.endpoint {trace}.input ({trace}.windows n)) =
      model.coordinates (n • generator) := by
  let completed := GroupFixedCircuitCompletion.run rho
    (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)
  have done := {trace}.actual_native_complete model rho n
    (GroupFixedWindows.fixedDigit (firstWitness (F := F) n) • generator) (4 • generator)
    one linked four imaginary nonSquare imaginarySquare inputMeaning baseMeaning bits
  have scalar := GroupFixedTemplateScalarDigits.folded_tail_value
    (firstWitness (F := F) n) (({trace}.windows n).map (fun window => window.witness completed))
    generator 252 n (actual_word completed n) bound
  exact ⟨done.1,done.2.1,done.2.2.trans (congrArg model.coordinates scalar)⟩

#print axioms actual_word
#print axioms actual_native_scalar_complete
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
