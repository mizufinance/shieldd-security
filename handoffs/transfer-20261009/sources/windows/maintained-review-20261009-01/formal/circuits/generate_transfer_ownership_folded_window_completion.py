"""Construct the first variable window's actual folded identity path.

The exact source/physical-row plan owns selector products and two one-write
linear assertions. It introduces no quotient witness or inverse assumption.
Native precompute/Boolean input meanings are subsequent explicit joins.
"""
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_completion as local
from .generate_hash_round import _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    if checked['metadata']['window_start'] != 0:
        raise completion.relation.RelationError('ownership folded constructor only initial window')
    identity = (('native', 0), ('native', 1))
    if any(point != identity for point in checked['windows'][0][:3]):
        raise completion.relation.RelationError('ownership folded exact initial identity doubles')
    plan = completion.window_plan(checked, extracted, 0, False, readonly_lcs)
    _folded_shape(checked,plan)
    old_name,source=local.generate(checked,extracted,0,False,readonly_lcs)
    return _finish(checked,old_name,source)


def render_folded(checked,extracted,plan,prefix):
    """Neutral first-identity exact folded row constructor."""
    _folded_shape(checked,plan)
    old_name,source=local.render_plan(checked,extracted,plan,prefix)
    return _finish(checked,old_name,source)


def _folded_shape(checked,plan):
    if plan.get('window_index',0)!=0 or any(point != (('native',0),('native',1)) for point in checked['windows'][0][:3]):
        raise completion.relation.RelationError('folded exact first identity source')
    groups = plan['point_groups']
    if len(groups) != 3 or any(group['stage_start'] != group['stage_end'] for group in groups[:2]):
        raise completion.relation.RelationError('ownership identity doubles own no witness stages')
    last = groups[2]
    stages = plan['stages'][last['material_end']:last['stage_end']]
    if len(stages) != 2 or any(stage['kind'] != 'linear' for stage in stages) or any(
            stage['kind'] not in ('square', 'product', 'linear') for stage in plan['stages']):
        raise completion.relation.RelationError('ownership initial add exact folded linear coordinates')


def _finish(checked,old_name,source):
    name = old_name.removesuffix('Completion') + 'FoldedCompletion'
    source = source.replace('ShielddSecurity.' + old_name, 'ShielddSecurity.' + name)
    ending = f'end ShielddSecurity.{name}\n'
    if not source.endswith(ending):
        raise completion.relation.RelationError('ownership folded maintained renderer namespace')
    source = source[:-len(ending)] + f'''theorem constructs {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (linked : base {checked['metadata']['constant_copy']} = base 0) :
    Satisfies (completeAssignment base) rawRows ∧
      (∀ column ∈ kept, completeAssignment base column = base column) := by
  apply local_rows_complete base linked
  simp [completionSteps,GroupCircuitCompletion.Legal,GroupCircuitCompletion.Step.Legal,
    CompilerCompletion.Step.Legal,Compiler.subtract,scaleLinear]
#print axioms constructs
{ending}'''
    return name, _signature_audits(source)
