"""Bind strict actual ordinary EPK windows to the existing symbolic program.

This is an additive alternative to the unchanged full local renderer. Each
returned local proof precedes its finite program adapter in module order.
"""
from . import generate_transfer_epk_fixed_completion as ingress
from . import generate_transfer_epk_fixed_template as template
from . import generate_transfer_fixed_spend as renderer
from . import transfer_relation as relation
from .generate_hash_round import linear


def generate_modules(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
                     scope_id,page_index=0,window_offset=0,*,readonly_lcs=()):
    checked,raw,normalized,_,_,plan,stem=ingress._selection(qualified_parent,raw_pages,
        accepted_capsules,accepted_roles,extracted,scope_id,page_index,window_offset,readonly_lcs)
    local=(stem+'TemplateCompletion',
        template.render_checked(checked,raw,normalized,plan,window_offset,stem=stem))
    adapter=render_checked(checked,raw,normalized,plan,window_offset,stem=stem)
    return [local,adapter]


def render_checked(checked,raw,normalized,plan,window_offset=0,*,stem):
    data=template._layout(checked,raw,normalized,plan,window_offset)
    local=stem+'TemplateCompletion';ns=stem+'TemplateProgram'
    # The endpoint must be the actual two quotient results. Verify coefficient
    # and column identity, never supply an equality of wanted coordinates.
    for endpoint,step in zip(data['after'],data['stages'][6:]):
        if tuple(endpoint)!=((step['quotient'],1),):
            raise relation.RelationError('EPK template program exact actual quotient endpoint')
    out=f'''import ShielddSecurity.{local}
import ShielddSecurity.GroupFixedWindowProgramTemplate
import ShielddSecurity.GroupFixedCircuitCompletion
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.{ns}

def program (low high : Bool) : GroupFixedCircuitCompletion.Program where
  stages := GroupFixedWindowProgramTemplate.stages {local}.stages {local}.x {local}.y
  rows := {local}.rawRows
  input := ({local}.layout.inputX,{local}.layout.inputY)
  output := ({linear(data['after'][0])},{linear(data['after'][1])})
  low := {local}.layout.low
  high := {local}.layout.high
  lowBit := low
  highBit := high

private theorem output_point {{F : Type}} [Field F] (rho : Nat → F) (low high : Bool) :
    GroupFixedCircuitCompletion.point rho (program low high).output =
      GroupQuotientPairCompletion.point {local}.x {local}.y rho := by
  simp only [program,GroupFixedCircuitCompletion.point,GroupQuotientPairCompletion.point,
    {local}.x,{local}.y,eval,Int.cast_one,one_mul,add_zero]

theorem local_constructor {{F : Type}} [Field F] [CharP F {local}.modulus]
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({local}.layout.d : F))
    (imaginarySquare : imaginary*imaginary = -1) (low high : Bool) :
    GroupFixedCircuitCompletion.LocalConstruct ({local}.layout.d : F)
      {local}.copyColumn (program low high) := by
  intro rho one linked incoming lowValue highValue
  change Group.OnCurve ({local}.layout.d : F) ({local}.layout.input rho) at incoming
  change eval rho {local}.layout.low = (if low then 1 else 0) at lowValue
  change eval rho {local}.layout.high = (if high then 1 else 0) at highValue
  have done := {local}.actual_window_complete rho one four linked imaginary nonSquare
    imaginarySquare low high lowValue highValue incoming
  have same : (program low high).build rho = {local}.completeAssignment rho :=
    GroupFixedWindowProgramTemplate.mixed_run rho {local}.stages {local}.x {local}.y
  constructor
  · change Satisfies ((program low high).build rho) {local}.rawRows
    rw [same]
    exact done.1
  · rw [same,output_point]
    exact done.2.1

theorem original_rows : (program false false).rows = {local}.rawRows := rfl

#print axioms local_constructor
#print axioms original_rows
end ShielddSecurity.{ns}
'''
    return ns,renderer._signature_audits(out)
