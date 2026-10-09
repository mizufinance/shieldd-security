"""Reuse the separately qualified actual folded first window as a prefix.

The native digit is derived from the constructed Boolean columns. No prefix
row truth, denominator legality or desired native output is a theorem premise.
"""
from . import transfer_epk_fixed_program as full
from . import generate_transfer_epk_fixed_completion as ingress
from . import generate_transfer_fixed_spend as render
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(parent,pages,capsules,roles,extracted,scope_id):
    accepted=full.plan(parent,pages,capsules,roles,extracted,scope_id)
    checked,_,_,_,_,plan,_=ingress._selection(
        parent,pages,capsules,roles,extracted['fixed'],scope_id,0,0,())
    first=plan['windows'][0]
    if first['index']!=0 or not first['folded_products']:
        raise relation.RelationError('EPK prefix requires actual initial folded window')
    bounds=accepted['bounds'];copy=bounds['constant_copy']
    stem=f'RuntimeTransferEpk{scope_id}FixedWindow000'
    old=stem+'Program';name=stem+'TemplatePrefix'
    source=render._window_program_source(checked,bounds['frames'][0],bounds,
        accepted['loop']['kept'],0,stem=stem)
    opening=f'namespace ShielddSecurity.{old}'
    closing=f'end ShielddSecurity.{old}'
    if source.count(opening)!=1 or source.count(closing)!=1:
        raise relation.RelationError('EPK exact folded program namespace')
    source=source.replace(opening,f'namespace ShielddSecurity.{name}')
    source=source.replace(closing,f'end ShielddSecurity.{name}')
    native=f'''theorem actual_native_prefix {{F J : Type}} [Field F] [CharP F {stem}.modulus]
    [AddCommGroup J] (model : Group.StandardCurveModel J ({stem}.coefficientD : F))
    (generator : J) (rho : Nat → F) (one : rho 0 = 1) (linked : rho {copy} = rho 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({stem}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (low high : Bool)
    (lowValue : eval rho {stem}.low = if low then 1 else 0)
    (highValue : eval rho {stem}.high = if high then 1 else 0)
    (baseMeaning : ({stem}.base : Group.Point F) = model.coordinates generator) :
    let completed := (program low high).build rho
    Satisfies completed {stem}.rawRows ∧
    (∀ column ∈ kept, completed column = rho column) ∧
    {stem}.output completed = model.coordinates ((low.toNat+2*high.toNat) • generator) ∧
    ({stem}.nextBase : Group.Point F) = model.coordinates (4 • generator) := by
  classical
  let completed := (program low high).build rho
  have incoming : GroupFixedCircuitCompletion.point rho (program low high).input =
      model.coordinates 0 := by
    rw [model.identity]
    simp [program,GroupFixedCircuitCompletion.point,Group.identityPoint,eval,one]
  have curved : Group.OnCurve ({stem}.coefficientD : F)
      (GroupFixedCircuitCompletion.point rho (program low high).input) := by
    rw [incoming]
    exact model.onCurve 0
  have done := local_constructor imaginary nonSquare imaginarySquare low high
    rho one linked curved lowValue highValue
  have preserves : ∀ column ∈ kept, completed column = rho column := by
    intro column member
    exact GroupCircuitOrder.run_outside rho (program low high).stages column
      (by intro stage present; exact caller_protected low high stage present column member)
  have oneBuilt : completed 0 = 1 := (preserves 0 (by decide)).trans one
  have lowBuilt : eval completed {stem}.low = if low then 1 else 0 := by
    have equal : eval completed {stem}.low = eval rho {stem}.low := by
      apply eval_agrees
      intro term member
      have checked : {stem}.low.all (fun term => decide (term.1 ∈ kept)) = true := by decide
      exact preserves term.1 (of_decide_eq_true (List.all_eq_true.mp checked term member))
    exact equal.trans lowValue
  have highBuilt : eval completed {stem}.high = if high then 1 else 0 := by
    have equal : eval completed {stem}.high = eval rho {stem}.high := by
      apply eval_agrees
      intro term member
      have checked : {stem}.high.all (fun term => decide (term.1 ∈ kept)) = true := by decide
      exact preserves term.1 (of_decide_eq_true (List.all_eq_true.mp checked term member))
    exact equal.trans highValue
  have inputMeaning : {stem}.input completed = model.coordinates 0 := by
    rw [model.identity]
    simp [{stem}.input,Group.identityPoint,eval,oneBuilt]
  have native := {stem}.actual_window_coordinates completed oneBuilt imaginary model
    nonSquare imaginarySquare 0 generator inputMeaning baseMeaning done.1
  have lowDecoded : ScalarBits.decodeBit completed {stem}.low = low := by
    cases low <;> simp [ScalarBits.decodeBit,lowBuilt]
  have highDecoded : ScalarBits.decodeBit completed {stem}.high = high := by
    cases high <;> simp [ScalarBits.decodeBit,highBuilt]
  refine ⟨done.1,preserves,?_,native.2⟩
  simpa only [{stem}.window,GroupFixedWindows.fixedDigit,lowDecoded,highDecoded,zero_add]
    using native.1
#print axioms actual_native_prefix
'''
    ending=f'end ShielddSecurity.{name}'
    source=source.replace(ending,native+ending)
    return name,_signature_audits(source)
