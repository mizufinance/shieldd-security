"""Construct only actual captured Poseidon round materializations.

The topological/coverage certificates are generated finite Lean obligations;
Python identity or support checks never replace their kernel qualification.
"""
from . import transfer_note_hash as hashes,transfer_arithmetic as arithmetic,transfer_relation as relation
from .transfer_balance_rows import canonical,combine,source_index
from .generate_hash_round import linear,_signature_audits,generate_selected_round


def _pivot(output,occupied):
    candidates=[c for c,v in output if v==1 and c not in occupied]
    if len(candidates)!=1:raise relation.RelationError('round completion fresh unit pivot absent/ambiguous')
    pivot=candidates[0];remainder=tuple((c,v) for c,v in output if c!=pivot)
    return pivot,remainder


def completion_plan(data,extracted,note_data,accepted_roles,parameter_root,index):
    index=relation.natural(index,65)
    selected=hashes.round_selection(data,extracted,note_data,accepted_roles,parameter_root)
    checked=hashes.inspect_metadata(data,note_data,accepted_roles,parameter_root)
    note=hashes.notes.inspect_metadata(note_data,accepted_roles)
    return _from_checked(selected,checked,note,index)


def _from_checked(selected,checked,note,index):
    """Internal bounded round adapter after complete DAG/row/parameter acceptance."""
    index=relation.natural(index,65)
    call=selected['calls'][0];segment=call['segments'][index]
    obj=checked['metadata'];copy=obj['constant_copy']
    raw={i:selected['rows'][i] for i in sorted(set(segment['rows'])|{selected['constant_link']})}
    normalized={i:tuple(canonical((0 if c==copy else c,v) for c,v in terms) for terms in row)
                for i,row in raw.items()}
    protected={0,1,2,copy}
    def protect(lc):protected.update(c for c,_ in lc)
    for lc in segment['before']:protect(lc)
    for ref in obj['hash']['inputs']:
        if 'source' in ref:protect(checked['observed'][source_index(ref['source'])])
    # Exogenous roles only. Commitment/NF/root/selector outputs are consumers
    # still under construction and must not be silently held fixed here.
    # Other owning typed ingresses provide their accepted exogenous LCs here.
    # They must enumerate actual source roles before invoking this emitter.
    for lc in note.get('readonly_lcs',[]):protect(lc)
    for spend in note['metadata'].get('spends',[]):
        refs=[*spend['note'],spend['position'],spend['dummy'],*spend['shared']['address'],
              *(spend['shared'][name] for name in ('asset','nk','randomizer','anchor'))]
        if spend['optional']:refs.append(spend['optional']['seed'])
        for ref in refs:
            if 'source' in ref:protect(note['observed'][source_index(ref['source'])])
        for name in ('amount_bits','position_bits'):
            for ref in spend[name]:protect(note['observed'][source_index(ref)])
    return _from_selected(selected, checked, index, [((column,1),) for column in sorted(protected)])


def _from_selected(selected, checked, index, readonly_lcs):
    """Shared arithmetic adapter after independent typed hash/row acceptance.

    The inputs remain derivative data, not an observer schema. Callers retain
    their own accepted source/parameter contracts and supply actual exogenous
    LCs. This routine never accepts a claimed final hash or prior row truth.
    """
    index=relation.natural(index,65)
    call=selected['calls'][0];segment=call['segments'][index]
    obj=checked['metadata'];copy=obj['constant_copy']
    raw={i:selected['rows'][i] for i in sorted(set(segment['rows'])|{selected['constant_link']})}
    normalized={i:tuple(canonical((0 if c==copy else c,v) for c,v in terms) for terms in row)
                for i,row in raw.items()}
    protected={0,1,2,copy}
    if not isinstance(readonly_lcs,(list,tuple)) or len(readonly_lcs)>4096:
        raise relation.RelationError('bounded hash constructor readonly LC inventory')
    for lc in list(segment['before'])+list(readonly_lcs):
        if not isinstance(lc,(list,tuple)) or len(lc)>4096:
            raise relation.RelationError('bounded hash constructor readonly LC')
        for term in lc:
            if not isinstance(term,(list,tuple)) or len(term)!=2:
                raise relation.RelationError('hash constructor readonly term shape')
            relation.natural(term[0],obj['domain_size'])
            if type(term[1]) is not int or not 0<term[1]<relation.MODULUS:
                raise relation.RelationError('hash constructor readonly term coefficient')
        if canonical(lc)!=tuple(tuple(term) for term in lc):
            raise relation.RelationError('hash constructor readonly LC canonical order')
        protected.update(c for c,_ in lc)
    steps=[];owned=set();prior_support=set();coverage={}
    def append(kind,left,right,output,indices,auxiliary=None):
        reads=left+(() if right is None else right)
        pivot,remainder=_pivot(output,protected|owned|prior_support|{c for c,_ in reads}|
                               (set() if auxiliary is None else {auxiliary}))
        writes={pivot}|(set() if auxiliary is None else {auxiliary})
        if (writes&(protected|owned|prior_support) or any(c in writes for c,_ in reads+remainder)):
            raise relation.RelationError('round completion forward/shared write support collision')
        if kind=='square':expected=[(left,canonical(((pivot,1),)+remainder))]
        else:expected=[(combine(left,right,-1),((auxiliary,1),)),
                       (combine(left,right),combine(((auxiliary,1),),output,4))]
        if any(normalized[i]!=body for i,body in zip(indices,expected)):
            raise relation.RelationError('round completion exact original constructor mismatch')
        if any(i in coverage for i in indices):raise relation.RelationError('round completion duplicated original row')
        for i,body in zip(indices,expected):coverage[i]=body
        steps.append(dict(kind=kind,left=left,right=right,remainder=remainder,output=pivot,
                          auxiliary=auxiliary,rows=indices))
        prior_support.update(c for c,_ in reads+remainder);prior_support.update(writes);owned.update(writes)
    for lane,cert in sorted(segment['fifths'].items()):
        if cert['kind']=='constant':continue
        base=segment['shifted'][lane];square=cert['square'];fourth=cert['fourth'];out=segment['transformed'][lane]
        sq=arithmetic.product_certificate(base,base,square,normalized)
        fourth_cert=arithmetic.product_certificate(square,square,fourth,normalized)
        fifth=arithmetic.product_certificate(fourth,base,out,normalized)
        if sq['kind']!='square' or fourth_cert['kind']!='square' or fifth['kind']!='product' or fifth['swapped']:
            raise relation.RelationError('round completion unsupported x2/x4/x5 lowering')
        auxiliary=fifth['auxiliary']
        if len(auxiliary)!=1 or auxiliary[0][1]!=1:
            raise relation.RelationError('round completion fresh unit auxiliary required')
        append('square',base,None,square,sq['rows'])
        append('square',square,None,fourth,fourth_cert['rows'])
        append('product',fourth,base,out,fifth['rows'],auxiliary[0][0])
    coverage[selected['constant_link']]=((),())
    if set(coverage)!=set(raw):raise relation.RelationError('round completion incomplete actual row coverage')
    return dict(selected=selected,checked=checked,segment=segment,steps=steps,kept=sorted(protected),
                writes=[c for step in steps for c in ([step['output']] if step['kind']=='square' else
                        [step['output'],step['auxiliary']])],raw=raw,coverage=coverage,index=index)


def generate(data,extracted,note_data,accepted_roles,parameter_root,index):
    """Return soundness dependency and local constructive source modules."""
    plan=completion_plan(data,extracted,note_data,accepted_roles,parameter_root,index)
    selected=plan['selected'];obj=plan['checked']['metadata'];role=selected['calls'][0]['role']
    base=f'RuntimeNoteHash{obj["slot"]}{obj["role"].capitalize()}{obj["level"]}Block{obj["block"]}Round{index}'
    sound=generate_selected_round(obj,selected,role,0,index,plan['checked']['metadata_sha256'])
    namespace='RuntimeHashRound_'+role.replace('.','_')+f'_0_{index}'
    out=f'''import ShielddSecurity.{base}Sound
import ShielddSecurity.PoseidonCompletion
import ShielddSecurity.CompilerOrder
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{base}Completion
open {namespace}
-- Local actual round construction only; all other Transfer rows remain OPEN.
def kept : List Nat := {plan['kept']}
def ownedWrites : List Nat := {plan['writes']}
def completionSteps : List CompilerCompletion.Step := [
'''
    definitions=[]
    for step in plan['steps']:
        if step['kind']=='square':definitions.append(f'.square ({linear(step["left"])}) ({linear(step["remainder"])}) {step["output"]}')
        else:definitions.append(f'.product ({linear(step["left"])}) ({linear(step["right"])}) ({linear(step["remainder"])}) {step["output"]} {step["auxiliary"]}')
    definitions.append('.equal [] []');out+='  '+',\n  '.join(definitions)+']\n'
    out+='''def completeAssignment {F : Type} [Field F] (rho : Nat → F) : Nat → F :=
  CompilerCompletion.run rho completionSteps
theorem ordered_checked : CompilerOrder.checkOrder kept [] completionSteps = true := by decide
theorem ordered : CompilerCompletion.Topological kept [] completionSteps :=
  CompilerOrder.checked_order kept [] completionSteps ordered_checked
theorem writes_exact : ∀ column, column ∈ PoseidonCompletion.writes completionSteps ↔ column ∈ ownedWrites := by
  intro column
  simp only [PoseidonCompletion.writes,completionSteps,ownedWrites,List.flatMap_cons,List.flatMap_nil,
    CompilerCompletion.Step.writes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
theorem legal_steps {F : Type} [Field F] (rho : Nat → F) : CompilerCompletion.Legal rho completionSteps := by
  simp [completionSteps,CompilerCompletion.Legal,CompilerCompletion.Step.Legal,eval]
theorem coverage_checked : rawRows.all (fun actual => (CompilerCompletion.emitted completionSteps).any
    (fun expected => decide (Compiler.canonical modulus (Compiler.unoutline '''+str(obj['constant_copy'])+''' actual.a) =
      Compiler.canonical modulus expected.a ∧ Compiler.canonical modulus (Compiler.unoutline '''+str(obj['constant_copy'])+''' actual.b) =
      Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ CompilerCompletion.emitted completionSteps,
    Compiler.canonical modulus (Compiler.unoutline '''+str(obj['constant_copy'])+''' actual.a) = Compiler.canonical modulus expected.a ∧
      Compiler.canonical modulus (Compiler.unoutline '''+str(obj['constant_copy'])+''' actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem preserves {F : Type} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  PoseidonCompletion.run_outside rho completionSteps column (fun member => outside ((writes_exact column).mp member))
theorem input_preserved {F : Type} [Field F] (rho : Nat → F) :
    (fun column => eval (completeAssignment rho) (before column)) = (fun column => eval rho (before column)) := by
  funext column
  apply PoseidonCompletion.eval_run_preserves rho completionSteps (before column)
  exact (by decide : ∀ column : Fin 6, ∀ term ∈ before column,
    term.1 ∉ PoseidonCompletion.writes completionSteps) column
theorem complete_round {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (linked : rho '''+str(obj['constant_copy'])+''' = rho 0) :
    Satisfies (completeAssignment rho) rawRows ∧
      (fun column => eval (completeAssignment rho) (after column)) =
        Poseidon.round (Poseidon.castParameters parameters) '''+str(index)+''' (fun column => eval rho (before column)) ∧
      (∀ column, column ∉ ownedWrites → completeAssignment rho column = rho column) := by
  have completed := CompilerCompletion.original_rows_complete rho completionSteps kept rawRows '''+str(obj['constant_copy'])+'''
    ordered (legal_steps rho) (by decide) (by decide) linked coverage
  have one' : completeAssignment rho 0 = 1 := (preserves rho 0 (by decide)).trans one
  have result := actual_round_sound (completeAssignment rho) one' completed.1
  rw [input_preserved rho] at result
  exact ⟨completed.1,result,preserves rho⟩
'''
    for name in ('ordered_checked','ordered','writes_exact','legal_steps','coverage_checked','coverage','preserves','input_preserved','complete_round'):
        out+=f'#print axioms {name}\n'
    out+=f'end ShielddSecurity.{base}Completion\n'
    return [(base+'Sound',sound),(base+'Completion',_signature_audits(out))]
