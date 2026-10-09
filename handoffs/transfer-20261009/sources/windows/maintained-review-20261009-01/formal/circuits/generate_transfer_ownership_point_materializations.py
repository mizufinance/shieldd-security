"""Construct each variable point's numerator/denominator/selection cones.

Only pure square/product stages run here. Their source formulas are then
derived from the constructed original rows before either coordinate division.
Later curve/coordinate sequencing must discharge those actual divisions.
"""
import re
from . import transfer_ownership_completion as completion
from . import generate_transfer_ownership_completion as local
from .generate_group_cones import generate_checked
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted, window_offset=0, include_precompute=True, readonly_lcs=()):
    plan = completion.window_plan(checked, extracted, window_offset, include_precompute, readonly_lcs)
    cones = completion.owner.cone_certificates(checked, extracted, window_offset, include_precompute)
    prefix = 'RuntimeRnkWindow' if checked['metadata'].get('schema') == 'shieldd-transfer-rnk-dh-v1' else 'RuntimeOwnershipWindow'
    return render_points(checked,plan,cones,prefix)


def render_points(checked,plan,cones,prefix):
    """Neutral exact checked-plan renderer; ingress owns schema/row validation."""
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',prefix) is None:
        raise completion.relation.RelationError('point materialization namespace')
    copy = checked['metadata']['constant_copy'];modulus = completion.relation.MODULUS
    modules = []
    for group in plan['point_groups']:
        name = prefix+f'{plan["window_index"]:03d}Point{group["index"]}'
        cone_name = name+'Cones'
        roles = {'formula'+str(i) for i in range(group['formula_start'],
                                                group['formula_start']+group['formula_count'])}
        selected_cones = [cone for cone in cones['cones'] if cone['role'] in roles]
        stages = plan['stages'][group['stage_start']:group['material_end']]
        if any(stage['kind'] not in ('square', 'product') for stage in stages):
            raise completion.relation.RelationError('ownership point materialization pure stage boundary')
        rows = {index for stage in stages for index in stage['rows']} | set(plan['constant_rows'])
        required = {index for cone in selected_cones for certificate in cone['certificates'].values()
                    for index in certificate.get('rows', [])} | set(plan['constant_rows'])
        if rows != required:
            raise completion.relation.RelationError('ownership point exact constructed source-cone coverage')
        selected = dict(cones, cones=selected_cones,
                        rows={index: cones['rows'][index] for index in sorted(rows)})
        source = generate_checked(selected, checked['metadata_sha256'],
                                  checked['metadata']['relation_digest'], namespace=cone_name,
                                  full_audits=True)
        modules.append((cone_name, source))
        writes = {column for stage in stages for column in
                  ([stage['output']] if stage['kind']=='square' else [stage['output'],stage['auxiliary']])}
        kept = set(plan['protected'])
        for cone in selected_cones:
            for identity in cone['inputs']:
                kept.update(column for column, _ in cones['observations'][identity][1] if column not in writes)
        if kept & writes:
            raise completion.relation.RelationError('ownership point materialization shared write')
        terms = [];expected = {}
        for stage in stages:
            term, literals = local.lower_stage(stage)
            terms.append(term);expected.update(zip(stage['rows'], literals))
        for index in plan['constant_rows']:expected[index] = '⟨[],[]⟩'
        terms.append('.compiler (.equal [] [])')
        name += 'Materializations'
        source = f'''import ShielddSecurity.{cone_name}
import ShielddSecurity.GroupCircuitOrder
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {modulus}
def kept : List Nat := {sorted(kept)}
def steps : List GroupCircuitCompletion.Step := ['''+','.join(terms)+f''']
def materialAssignment {{F : Type}} [Field F] (base : Nat → F) : Nat → F :=
  GroupCircuitCompletion.run base steps
theorem material_ordered : GroupCircuitCompletion.Topological kept [] steps :=
  GroupCircuitOrder.checked_order kept [] steps (by decide)
private theorem material_legal {{F : Type}} [Field F] (base : Nat → F) :
    GroupCircuitCompletion.Legal base steps := by
  simp [steps,GroupCircuitCompletion.Legal,GroupCircuitCompletion.Step.Legal,CompilerCompletion.Step.Legal,
    Compiler.subtract,scaleLinear]
theorem original_coverage : ∀ actual ∈ {cone_name}.rawRows, ∃ expected ∈ GroupCircuitCompletion.emitted steps,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [{cone_name}.rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in sorted(rows))+'\n'
        for index in sorted(rows):
            source += f'''  · refine ⟨{expected[index]}, ?_, by decide, by decide⟩
    simp [steps,GroupCircuitCompletion.emitted,GroupCircuitCompletion.Step.rows,
      CompilerCompletion.Step.rows,CompilerCompletion.squareRows,ScalarCompletion.productRows,
      Compiler.subtract,scaleLinear]
'''
        source += f'''theorem material_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (linked : base {copy} = base 0) :
    Satisfies (materialAssignment base) {cone_name}.rawRows ∧
      (∀ column ∈ kept, materialAssignment base column = base column) :=
  GroupCircuitCompletion.original_rows_complete base steps kept {cone_name}.rawRows {copy}
    material_ordered (material_legal base) (by decide) (by decide) linked original_coverage
'''
        # Source-formula conclusions are the already maintained independent
        # graph expressions. Substitute the constructed assignment; no initial
        # satisfaction or guessed result is added to their premises.
        for cone in selected_cones:
            role = cone['role']
            original = modules[-1][1]
            anchor = 'theorem '+role+'_sound '
            start = original.index(anchor)
            end = original.index(' := by', start)
            statement = original[start:end]
            match = re.search(r':\s*eval rho (.+)$', statement, re.S)
            if match is None:
                raise completion.relation.RelationError('ownership point source-formula conclusion shape')
            conclusion = 'eval (materialAssignment base) '+re.sub(
                r'\brho\b', '(materialAssignment base)', match.group(1))
            source += f'''theorem {role}_constructed {{F : Type}} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = base 0) :
    {conclusion} := by
  have complete := material_rows_complete base linked
  have materialOne : materialAssignment base 0 = 1 := (complete.2 0 (by decide)).trans one
  exact {cone_name}.{role}_sound (materialAssignment base) materialOne complete.1
'''
        for export in ('material_ordered', 'original_coverage', 'material_rows_complete',
                       *(cone['role']+'_constructed' for cone in selected_cones)):
            source += '#print axioms '+export+'\n'
        # Qualify cone LC definitions only; module-local declarations retain
        # their own names. The expression is taken from the checked renderer.
        for declaration in re.findall(r'^def (formula[0-9]+_[A-Za-z0-9_]+) : Linear :=', modules[-1][1], re.M):
            source = re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(declaration)+r'\b', cone_name+'.'+declaration, source)
        modules.append((name, _signature_audits(source+f'end ShielddSecurity.{name}\n')))
    return modules
