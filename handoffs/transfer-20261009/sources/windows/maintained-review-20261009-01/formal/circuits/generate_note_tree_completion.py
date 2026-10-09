"""Construct the six owned products of one actual quaternary tree level.

Position bits come from the independently completed range stage. Hashing its
children and completing the full path are subsequent stages, not premises.
"""
from . import transfer_note_tree as tree,transfer_note_spend as notes,transfer_relation as relation
from . import transfer_arithmetic as arithmetic
from .generate_hash_round import linear,_signature_audits
from .generate_note_hash_block_completion import _step


def completion_plan(data,extracted,note_data,accepted_roles):
    selected=tree.certificates(data,extracted,note_data,accepted_roles)
    current=selected['checked']['levels'][selected['slot']*24+selected['level']]
    kept={0,1,2,selected['checked']['metadata']['constant_copy']}
    for lc in accepted_roles['observed'].values():kept.update(c for c,_ in lc)
    for lc in notes.inspect_metadata(note_data,accepted_roles)['observed'].values():kept.update(c for c,_ in lc)
    for lc in [current['node'],current['low'],current['high'],*current['siblings']]:kept.update(c for c,_ in lc)
    steps=[];writes=[];prior_support=set()
    for (left,right,output),cert in zip(current['products'],selected['products']):
        step=arithmetic.product_completion_certificate(left,right,output,cert,selected['rows'])
        if step is None:raise relation.RelationError('tree completion needs exact fresh unit product/auxiliary')
        owned={step['output'],step['auxiliary']}
        if owned&(kept|set(writes)|prior_support):
            raise relation.RelationError('tree completion write touches shared or prior actual-row support')
        step['kind']='product';steps.append(step);writes.extend([step['output'],step['auxiliary']])
        prior_support.update(c for i in step['rows'] for terms in selected['rows'][i] for c,_ in terms)
    return dict(selected=selected,current=current,steps=steps,writes=writes,kept=sorted(kept))


def generate(data,extracted,note_data,accepted_roles):
    plan=completion_plan(data,extracted,note_data,accepted_roles);selected=plan['selected']
    base=f'RuntimeTransferNoteTree{selected["slot"]}Level{selected["level"]}';name=base+'Completion'
    copy=selected['checked']['metadata']['constant_copy']
    source=f'''import ShielddSecurity.{base}
import ShielddSecurity.CompilerOrder
import ShielddSecurity.PoseidonCompletion
import ShielddSecurity.TreeTrace
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
open {base}
-- Exact local15row construction; native position/path/hash joins OPEN.
def kept : List Nat := {plan['kept']}
def ownedWrites : List Nat := {plan['writes']}
def completionSteps : List CompilerCompletion.Step := [
'''
    source+='  '+',\n  '.join([_step(step) for step in plan['steps']]+
                             ['.squareEqual low low','.squareEqual high high','.equal [] []'])+']\n'
    source+='''def completeAssignment {F : Type} [Field F] (rho : Nat → F) : Nat → F :=
  CompilerCompletion.run rho completionSteps
theorem ordered_checked : CompilerOrder.checkOrder kept [] completionSteps = true := by decide
theorem ordered : CompilerCompletion.Topological kept [] completionSteps :=
  CompilerOrder.checked_order kept [] completionSteps ordered_checked
theorem writes_exact : ∀ column, column ∈ PoseidonCompletion.writes completionSteps ↔ column ∈ ownedWrites := by
  intro column
  simp only [PoseidonCompletion.writes,completionSteps,ownedWrites,List.flatMap_cons,List.flatMap_nil,
    CompilerCompletion.Step.writes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
theorem preserves {F : Type} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  PoseidonCompletion.run_outside rho completionSteps column (fun member => outside ((writes_exact column).mp member))
theorem kept_value {F : Type} [Field F] (rho : Nat → F) (terms : Linear)
    (checked : terms.all (fun term => decide (term.1 ∈ kept)) = true) :
    eval (completeAssignment rho) terms = eval rho terms := by
  apply eval_agrees
  intro term member
  exact CompilerCompletion.run_preserves rho completionSteps kept [] ordered term.1
    (of_decide_eq_true ((List.all_eq_true.mp checked) term member))
theorem legal_steps {F : Type} [Field F] (rho : Nat → F) (lo hi : Bool)
    (lowValue : eval rho low = Tree.bit lo) (highValue : eval rho high = Tree.bit hi) :
    CompilerCompletion.Legal rho completionSteps := by
  have lowComplete : eval (completeAssignment rho) low = Tree.bit lo :=
    (kept_value rho low (by decide)).trans lowValue
  have highComplete : eval (completeAssignment rho) high = Tree.bit hi :=
    (kept_value rho high (by decide)).trans highValue
  have lowBoolean : Square (eval (completeAssignment rho) low) (eval (completeAssignment rho) low) := by
    rw [lowComplete]
    cases lo <;> simp [Square,Tree.bit]
  have highBoolean : Square (eval (completeAssignment rho) high) (eval (completeAssignment rho) high) := by
    rw [highComplete]
    cases hi <;> simp [Square,Tree.bit]
  simp only [completionSteps,CompilerCompletion.Legal,CompilerCompletion.Step.Legal,CompilerCompletion.Step.run]
  exact ⟨trivial,trivial,trivial,trivial,trivial,trivial,lowBoolean,highBoolean,trivial,trivial⟩
'''
    source+=f'''theorem coverage_checked : rawRows.all (fun actual => (CompilerCompletion.emitted completionSteps).any
    (fun expected => decide (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) =
      Compiler.canonical modulus expected.a ∧ Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) =
      Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ CompilerCompletion.emitted completionSteps,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem complete_level {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0) (lo hi : Bool)
    (lowValue : eval rho low = Tree.bit lo) (highValue : eval rho high = Tree.bit hi) :
    Satisfies (completeAssignment rho) rawRows ∧
      [eval (completeAssignment rho) child0,eval (completeAssignment rho) child1,
       eval (completeAssignment rho) child2,eval (completeAssignment rho) child3] =
        Tree.children lo hi (eval rho node) (eval rho sibling0) (eval rho sibling1) (eval rho sibling2) ∧
      (∀ column, column ∉ ownedWrites → completeAssignment rho column = rho column) := by
  have completed := (CompilerCompletion.original_rows_complete rho completionSteps kept rawRows {copy}
    ordered (legal_steps rho lo hi lowValue highValue) (by decide) (by decide) linked coverage).1
  obtain ⟨a,b,ha,hb,children⟩ := ordered_children (completeAssignment rho) four completed
  have lowComplete : eval (completeAssignment rho) low = Tree.bit lo :=
    (kept_value rho low (by decide)).trans lowValue
  have highComplete : eval (completeAssignment rho) high = Tree.bit hi :=
    (kept_value rho high (by decide)).trans highValue
  have aEqual : a = lo := by
    have bits := congrArg TreeTrace.bitOf (ha.trans lowComplete)
    simpa only [TreeTrace.bitOf_of_bit] using bits
  have bEqual : b = hi := by
    have bits := congrArg TreeTrace.bitOf (hb.trans highComplete)
    simpa only [TreeTrace.bitOf_of_bit] using bits
  rw [aEqual,bEqual,kept_value rho node (by decide),kept_value rho sibling0 (by decide),
    kept_value rho sibling1 (by decide),kept_value rho sibling2 (by decide)] at children
  exact ⟨completed,children,preserves rho⟩
'''
    for export in ('ordered_checked','ordered','writes_exact','preserves','kept_value','legal_steps',
                   'coverage_checked','coverage','complete_level'):source+=f'#print axioms {export}\n'
    return [(base,tree.generate_level(data,extracted,note_data,accepted_roles)),
            (name,_signature_audits(source+f'end ShielddSecurity.{name}\n'))]
