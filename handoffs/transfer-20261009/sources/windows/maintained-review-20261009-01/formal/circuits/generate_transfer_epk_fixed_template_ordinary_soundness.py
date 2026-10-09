"""Apply checked ordinary EPK trace soundness to an arbitrary row assignment.

The exact retained union is accepted again. Native scalar decoding, the folded
prefix and projection from the complete carrier remain separate obligations.
"""
from . import transfer_epk_fixed_program as full, transfer_fixed_spend as fixed
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits, signed


def generate(parent, pages, capsules, roles, extracted, scope_id):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    if (len(accepted['chunks']) != 8 or
            [c['metadata']['window_start'] for c in accepted['chunks']] != list(range(0, 126, 16)) or
            len(accepted['loop']['programs']) != 126):
        raise relation.RelationError('EPK soundness exact eight-page126 source inventory')
    copy = accepted['bounds']['constant_copy']
    d = signed(fixed.D)
    trace = f'RuntimeTransferEpk{scope_id}FixedTemplateOrdinaryTrace'
    ns = f'RuntimeTransferEpk{scope_id}FixedTemplateOrdinarySoundness'
    source = f'''import ShielddSecurity.{trace}
import ShielddSecurity.GroupFixedTemplateNativeSoundness
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 100000

theorem actual_native_sound {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (acc generator : J)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho {trace}.input = model.coordinates acc)
    (baseMeaning : GroupFixedWindowTemplate.castPoint {trace}.base = model.coordinates generator)
    (rows : Satisfies rho (GroupFixedCircuitCompletion.rows
      (({trace}.windows n).map GroupFixedTemplateTrace.Window.program)))
    (bits : ∀ window ∈ {trace}.windows n,
      eval rho window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval rho window.program.high = (if window.program.highBit then 1 else 0)) :
    GroupFixedCircuitCompletion.point rho
      (GroupFixedTemplateTrace.endpoint {trace}.input ({trace}.windows n)) =
      model.coordinates (acc + TransferWindows.digitsValue
        ((({trace}.windows n).map (fun window => window.witness rho)).map
          GroupFixedWindows.fixedDigit) • generator) :=
  GroupFixedTemplateNativeSoundness.checked_native {copy} {d} model rho
    ({trace}.windows n) {trace}.input {trace}.base acc generator one four imaginary
    nonSquare imaginarySquare inputMeaning baseMeaning ({trace}.aligned n)
    ({trace}.checked n) rows bits

#print axioms actual_native_sound
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
