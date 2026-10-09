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
    copy, high = accepted['bounds']['constant_copy'], accepted['bounds']['high_start']
    d = signed(fixed.D)
    trace = f'RuntimeBalanceBlindingTemplateOrdinaryTrace'
    before = f'RuntimeBalanceBlindingWindow001TemplateTrace.before'
    ns = f'RuntimeBalanceBlindingTemplateOrdinaryPrior'
    source = f'''import ShielddSecurity.{trace}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

theorem prior_fresh (n : Nat) (prior : List Row)
    (covered : GroupFixedCircuitBounds.RowsCovered {high} {copy} {before} prior) :
    GroupFixedCircuitCompletion.Fresh prior
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program) := by
  have result := GroupFixedCircuitBounds.bounded_fresh {high} {copy} {before}
    prior ({trace}.segments n) covered ({trace}.certified_bounds n)
  rw [{trace}.segments_programs] at result
  exact result

theorem actual_native_complete_prior {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (acc generator : J) (prior : List Row)
    (covered : GroupFixedCircuitBounds.RowsCovered {high} {copy} {before} prior)
    (initial : Satisfies rho prior)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho {trace}.input = model.coordinates acc)
    (baseMeaning : GroupFixedWindowTemplate.castPoint {trace}.base = model.coordinates generator)
    (bits : ∀ program ∈ ({trace}.windows n).map GroupFixedTemplateTrace.Window.program,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    let completed := GroupFixedCircuitCompletion.run rho
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)
    Satisfies completed (prior ++ GroupFixedCircuitCompletion.rows
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)) ∧
    (∀ column ∈ {trace}.kept, completed column = rho column) ∧
    GroupFixedCircuitCompletion.point completed
      (GroupFixedTemplateTrace.endpoint {trace}.input ({trace}.windows n)) =
      model.coordinates (acc + TransferWindows.digitsValue
        ((({trace}.windows n).map (fun window => window.witness completed)).map
          GroupFixedWindows.fixedDigit) • generator) := by
  have constructors : ∀ program ∈ ({trace}.windows n).map GroupFixedTemplateTrace.Window.program,
      GroupFixedCircuitCompletion.LocalConstruct (({d} : Int) : F) {copy} program := by
    intro program member
    obtain ⟨window,present,rfl⟩ := List.mem_map.mp member
    exact {trace}.constructors four imaginary nonSquare imaginarySquare n window present
  have incoming : Group.OnCurve (({d} : Int) : F)
      (GroupFixedCircuitCompletion.point rho {trace}.input) := by
    rw [inputMeaning]
    exact model.onCurve acc
  have done := GroupFixedCircuitCompletion.constructs (({d} : Int) : F) {copy} rho
    (({trace}.windows n).map GroupFixedTemplateTrace.Window.program) {trace}.input prior {trace}.kept
    constructors ({trace}.caller_protected n) ({trace}.bit_supports n)
    (prior_fresh n prior covered) ({trace}.program_aligned n) (by decide) (by decide)
    one linked initial incoming bits
  have native := {trace}.actual_native_complete model rho n acc generator one linked
    four imaginary nonSquare imaginarySquare inputMeaning baseMeaning bits
  exact ⟨done.1,native.2.1,native.2.2⟩

#print axioms prior_fresh
#print axioms actual_native_complete_prior
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
