"""Bounded actual-row construction of a captured one-block note hash.

Each group owns only exact x2/x4/x5 materializations. Later writes must preserve
all earlier original rows. Closed DAG/parameter/row checks remain mandatory;
emitted sources are candidates until their named kernel audits pass.
"""
from . import generate_note_hash_completion as rounds,transfer_note_hash_join as joins
from . import transfer_relation as relation
from .generate_hash_round import linear,_signature_audits


def chunk_plan(data,extracted,note_data,accepted_roles,parameter_root,start,stop):
    return _chunk_plan(_context(data,extracted,note_data,accepted_roles,parameter_root),start,stop)


def _context(data,extracted,note_data,accepted_roles,parameter_root):
    return (rounds.hashes.round_selection(data,extracted,note_data,accepted_roles,parameter_root),
            rounds.hashes.inspect_metadata(data,note_data,accepted_roles,parameter_root),
            rounds.hashes.notes.inspect_metadata(note_data,accepted_roles))


def _chunk_plan(context,start,stop,*,readonly_lcs=None):
    start=relation.natural(start,65);stop=relation.natural(stop,66)
    if not start<stop<=min(65,start+5):
        raise relation.RelationError('note completion chunk requires one to five ascending rounds')
    first=None;steps=[];raw={};owned=[];prior_support=set();kept=set()
    for i in range(start,stop):
        plan=(rounds._from_checked(*context,i) if readonly_lcs is None else
              rounds._from_selected(context[0],context[1],i,readonly_lcs))
        if first is None:first=plan;kept=set(plan['kept'])
        for step in plan['steps']:
            writes=[step['output']]+([] if step['kind']=='square' else [step['auxiliary']])
            reads=step['left']+step['remainder']+(step['right'] or ())
            if set(writes)&(kept|prior_support|set(owned)|{c for c,_ in reads}):
                raise relation.RelationError('note completion cross-round write aliases prior/shared support')
            prior_support.update(c for i in step['rows'] for terms in plan['raw'][i] for c,_ in terms)
            owned.extend(writes);steps.append(step)
        for index,row in plan['raw'].items():
            if index in raw and raw[index]!=row:
                raise relation.RelationError('note completion chunk inconsistent actual row identity')
            raw[index]=row
    return dict(start=start,stop=stop,steps=steps,raw=dict(sorted(raw.items())),writes=owned,
                kept=sorted(kept),selected=first['selected'],checked=first['checked'])


def _step(step):
    if step['kind']=='square':
        return f'.square ({linear(step["left"])}) ({linear(step["remainder"])}) {step["output"]}'
    return (f'.product ({linear(step["left"])}) ({linear(step["right"])}) '
            f'({linear(step["remainder"])}) {step["output"]} {step["auxiliary"]}')


def _partition_order_source(plan):
    """Symbolically combine small round certificates with linear prior fences."""
    parts=[];support=set();fences=[];copy=plan['checked']['metadata']['constant_copy']
    for index in range(plan['start'],plan['stop']):
        rows=set(plan['selected']['calls'][0]['segments'][index]['rows'])
        steps=[step for step in plan['steps'] if set(step['rows'])<=rows]
        writes=[c for step in steps for c in
            ([step['output']] if step['kind']=='square' else [step['output'],step['auxiliary']])]
        if not writes:return None
        floor=min(writes)
        if any(c!=copy and c>=floor for c in support) or copy in writes:return None
        parts.append(steps);fences.append(floor)
        support.update(0 if c==copy else c for i in rows for terms in plan['raw'][i] for c,_ in terms)
    if [step for part in parts for step in part]!=plan['steps']:
        raise relation.RelationError('hash round order partition does not cover exact steps')
    source=''
    for i,steps in enumerate(parts):
        bodies=[_step(step) for step in steps]
        if i==len(parts)-1:bodies.append('.equal [] []')
        source+=f'def partSteps{i} : List CompilerCompletion.Step := [\n  '+',\n  '.join(bodies)+']\n'
        source+=f'def prefixSteps{i} : List CompilerCompletion.Step := '+(
            f'prefixSteps{i-1} ++ partSteps{i}' if i else 'partSteps0')+'\n'
    source+='theorem ordered : CompilerCompletion.Topological kept [] completionSteps := by\n'
    for i,_ in enumerate(parts):
        source+=f'''  have checked{i} : CompilerOrder.checkOrder kept [] partSteps{i} = true := by decide
  have localOrder{i} := CompilerOrder.checked_order kept [] partSteps{i} checked{i}
'''
        if not i:
            source+='  have joined0 : CompilerCompletion.Topological kept [] prefixSteps0 := localOrder0\n'
            continue
        source+=f'''  have lower{i} : ColumnFence.checkWrites {copy} {fences[i]} (PoseidonCompletion.writes partSteps{i}) = true := by decide
  have upper{i} : ColumnFence.checkRows {copy} {fences[i]} (CompilerCompletion.emitted prefixSteps{i-1}) = true := by decide
  have outside{i} := ColumnFence.checked_rows {copy} {fences[i]} (PoseidonCompletion.writes partSteps{i})
    (CompilerCompletion.emitted prefixSteps{i-1}) lower{i} upper{i}
  have extended{i} : CompilerCompletion.Topological kept (CompilerCompletion.emitted prefixSteps{i-1}) partSteps{i} := by
    have extension := CompilerOrderComposition.extend kept [] (CompilerCompletion.emitted prefixSteps{i-1})
      partSteps{i} localOrder{i} (by
        intro row member term present step found written
        exact outside{i} row member term present (List.mem_flatMap.mpr ⟨step,found,written⟩))
    simpa only [List.append_nil] using extension
  have joined{i} : CompilerCompletion.Topological kept [] prefixSteps{i} :=
    CompilerOrderComposition.append kept [] prefixSteps{i-1} partSteps{i} joined{i-1} extended{i}
'''
    source+=f'''  have partition : completionSteps = prefixSteps{len(parts)-1} := by rfl
  rw [partition]
  exact joined{len(parts)-1}
theorem ordered_checked : CompilerOrder.checkOrder kept [] completionSteps = true :=
  CompilerOrderComposition.check_order kept [] completionSteps ordered
'''
    return source


def _chunk_source(base,index,plan,prior):
    obj=plan['checked']['metadata'];name=base+f'CompletionChunk{index}'
    floor=min(plan['writes']);copy=obj['constant_copy']
    earlier={i for segment in plan['selected']['calls'][0]['segments'][:plan['start']] for i in segment['rows']}
    if prior:earlier.add(plan['selected']['constant_link'])
    bounded=(len(prior)>=12 and copy not in plan['writes'] and all(
        c==copy or c<floor for i in earlier for terms in plan['selected']['rows'][i] for c,_ in terms))
    source='import ShielddSecurity.PoseidonCompletion\nimport ShielddSecurity.CompilerOrder\n'
    partition=_partition_order_source(plan) if len(prior)>=12 else None
    if bounded or partition is not None:source+='import ShielddSecurity.ColumnFence\n'
    if partition is not None:source+='import ShielddSecurity.CompilerOrderComposition\n'
    source+=''.join(f'import ShielddSecurity.{module}\n' for module in prior)
    source+=f'''set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Actual rounds {plan['start']}..{plan['stop']-1}; no whole Transfer completion claim.
def modulus : Nat := {relation.MODULUS}
def kept : List Nat := {plan['kept']}
def ownedWrites : List Nat := {plan['writes']}
def rawRows : List Row := [
'''
    source+=',\n'.join('  ⟨'+linear(a)+','+linear(b)+'⟩' for a,b in plan['raw'].values())+']\n'
    source+='def priorRows : List Row := '+(' ++ '.join(p+'.rawRows' for p in prior) or '[]')+'\n'
    source+='def completionSteps : List CompilerCompletion.Step := [\n  '+',\n  '.join(
        [_step(s) for s in plan['steps']]+['.equal [] []'])+']\n'
    source+='''def completeAssignment {F : Type} [Field F] (rho : Nat → F) : Nat → F :=
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
'''
    source+=f'''theorem coverage_checked : rawRows.all (fun actual => (CompilerCompletion.emitted completionSteps).any
    (fun expected => decide (Compiler.canonical modulus (Compiler.unoutline {obj['constant_copy']} actual.a) =
      Compiler.canonical modulus expected.a ∧ Compiler.canonical modulus (Compiler.unoutline {obj['constant_copy']} actual.b) =
      Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ CompilerCompletion.emitted completionSteps,
    Compiler.canonical modulus (Compiler.unoutline {obj['constant_copy']} actual.a) = Compiler.canonical modulus expected.a ∧
      Compiler.canonical modulus (Compiler.unoutline {obj['constant_copy']} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  PoseidonCompletion.run_outside rho completionSteps column (fun member => outside ((writes_exact column).mp member))
theorem complete {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {obj['constant_copy']} = rho 0) : Satisfies (completeAssignment rho) rawRows :=
  (CompilerCompletion.original_rows_complete rho completionSteps kept rawRows {obj['constant_copy']}
    ordered (legal_steps rho) (by decide) (by decide) linked coverage).1
theorem prior_support_checked : priorRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ ownedWrites))) = true := by decide
theorem prior_preserved {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho priorRows) : Satisfies (completeAssignment rho) priorRows := by
  intro row member
  have outside : ∀ term ∈ row.a ++ row.b, term.1 ∉ PoseidonCompletion.writes completionSteps := by
    intro term present written
    have absent := of_decide_eq_true
      ((List.all_eq_true.mp ((List.all_eq_true.mp prior_support_checked) row member)) term present)
    exact absent ((writes_exact term.1).mp written)
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (completeAssignment rho) terms = eval rho terms :=
    PoseidonCompletion.eval_run_preserves rho completionSteps terms
      (fun term present => outside term (included term present))
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact satisfied row member
'''
    if bounded:
        old='''theorem prior_support_checked : priorRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ ownedWrites))) = true := by decide'''
        new=f'''theorem prior_support_checked : priorRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ ownedWrites))) = true := by
  have lower : ColumnFence.checkWrites {copy} {floor} ownedWrites = true := by decide
  have upper : ColumnFence.checkRows {copy} {floor} priorRows = true := by decide
  have absent := ColumnFence.checked_rows {copy} {floor} ownedWrites priorRows lower upper
  apply List.all_eq_true.mpr
  intro row member
  apply List.all_eq_true.mpr
  intro term present
  simpa only [decide_eq_true_eq] using absent row member term present'''
        if source.count(old)!=1:raise relation.RelationError('bounded hash support proof source anchor')
        source=source.replace(old,new)
    if partition is not None:
        old='''theorem ordered_checked : CompilerOrder.checkOrder kept [] completionSteps = true := by decide
theorem ordered : CompilerCompletion.Topological kept [] completionSteps :=
  CompilerOrder.checked_order kept [] completionSteps ordered_checked
'''
        if source.count(old)!=1:raise relation.RelationError('partitioned hash order source anchor')
        source=source.replace(old,partition)
    for export in ('ordered_checked','ordered','writes_exact','legal_steps','coverage_checked','coverage','preserves','complete',
                   'prior_support_checked','prior_preserved'):source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def generate(data,extracted,note_data,accepted_roles,parameter_root,on_chunk=None,
             *,linear_declarations_per_module=None):
    """Yield bounded dependencies then a constructive whole one-block call join."""
    call=joins.inspect_calls([data],note_data,accepted_roles)[0]['metadata']
    if call['block']!=0 or call['role']=='commitment':
        raise relation.RelationError('note completion currently requires a complete one-block call')
    base=f'RuntimeNoteHash{call["slot"]}{call["role"].capitalize()}{call["level"]}'
    for module,source in joins.generate([data],[extracted],note_data,accepted_roles,parameter_root,
        linear_declarations_per_module=linear_declarations_per_module):
        yield module,source
    context=_context(data,extracted,note_data,accepted_roles,parameter_root)
    prior=[];prior_support=set();owned=set();all_rows={};expected_rows=None
    for index,start in enumerate(range(0,65,5)):
        plan=_chunk_plan(context,start,min(start+5,65))
        if set(plan['writes'])&(prior_support|owned):
            raise relation.RelationError('note completion later chunk changes earlier actual row support')
        prior_support.update(c for row in plan['raw'].values() for terms in row for c,_ in terms)
        owned.update(plan['writes']);all_rows.update(plan['raw'])
        if expected_rows is None:expected_rows=set(plan['selected']['rows'])
        if on_chunk is not None:on_chunk(index,plan)
        module,source=_chunk_source(base,index,plan,prior)
        yield module,source;prior.append(module)
    if set(all_rows)!=expected_rows:
        raise relation.RelationError('note completion incomplete full captured block row coverage')
    yield base+'Completion',_composition(base,prior,call)


def _composition(base,chunks,obj,*,rows_only=False,sound_module=None,sound_namespace=None,width=6,
                 permutation_namespace=None):
    name=base+'Completion';last=chunks[-1];copy=obj['constant_copy']
    sound_module=sound_module or base;sound_namespace=sound_namespace or base
    permutation=permutation_namespace or (sound_namespace if rows_only else
        f'RuntimeHashBlock_spend{obj["slot"]}_{obj["role"]}{obj["level"]}_permutation{obj["block"]}_0')
    source=f'import ShielddSecurity.{sound_module}\n'+''.join(f'import ShielddSecurity.{chunk}\n' for chunk in chunks)
    source+=f'''set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Complete captured one-block hash only; native byte and whole Transfer joins OPEN.
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := {last}.priorRows ++ {last}.rawRows
def chunkWrites : Nat → List Nat := fun index => match index with
'''
    for i,chunk in enumerate(chunks):source+=f'  | {i} => {chunk}.ownedWrites\n'
    source+='  | _ => []\ndef ownedWrites : List Nat := (List.range 13).flatMap chunkWrites\n'
    source+='def assignment0 {F : Type} [Field F] (rho : Nat → F) : Nat → F := rho\n'
    for i,chunk in enumerate(chunks):
        source+=f'def assignment{i+1} {{F : Type}} [Field F] (rho : Nat → F) : Nat → F := {chunk}.completeAssignment (assignment{i} rho)\n'
    source+='def completeAssignment {F : Type} [Field F] (rho : Nat → F) : Nat → F := assignment13 rho\n'
    source+=f'''theorem sound_coverage_checked : {sound_namespace}.rawRows.all (fun row => decide (row ∈ rawRows)) = true := by
'''
    # Lean ++ is left associative. Check each bounded round locally, then use
    # one symbolic chunk inclusion (instead of repeating all append layers).
    for chunk in range(13):
        present='member'
        if chunk:
            present=f'List.mem_append.mpr (Or.inr ({present}))'
        for _ in range(12-chunk):present=f'List.mem_append.mpr (Or.inl ({present}))'
        source+=f'''  have chunkIncluded{chunk} : ∀ row ∈ {chunks[chunk]}.rawRows, row ∈ rawRows := by
    intro row member
    exact {present}
'''
    source+=f'''  have included : ∀ i : Fin 65, ∀ row ∈ {permutation}.rawRoundRows i.val, row ∈ rawRows := by
    '''
    for i in range(65):
        indent='    '+'  '*i;chunk=i//5
        source+='refine Fin.cases ?_ ?_\n'+indent+'· intro row member\n'
        source+=indent+f'  have localRows : List.Sublist ({permutation}.rawRoundRows {i}) {chunks[chunk]}.rawRows := by decide\n'
        source+=indent+f'  exact chunkIncluded{chunk} row (localRows.subset member)\n'+indent+'· '
    source+='intro impossible; exact Fin.elim0 impossible\n'
    source+=f'''  apply List.all_eq_true.mpr
  intro row member
  change row ∈ (List.range 65).flatMap {permutation}.rawRoundRows at member
  obtain ⟨i,bound,present⟩ := List.mem_flatMap.mp member
  simpa only [decide_eq_true_eq] using included ⟨i,List.mem_range.mp bound⟩ row present
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column := by
'''
    for i,chunk in enumerate(chunks):
        source+=f'''  have outside{i} : column ∉ {chunk}.ownedWrites := by
    intro member
    exact outside (List.mem_flatMap.mpr ⟨{i},by decide,member⟩)
  have same{i} : assignment{i+1} rho column = assignment{i} rho column := {chunk}.preserves (assignment{i} rho) column outside{i}
'''
    source+='  exact '+'.trans '.join(f'same{i}' for i in reversed(range(13)))+'\n'
    # Parentheses are needed for a long transitive chain: associate explicitly.
    source=source.replace('  exact '+'.trans '.join(f'same{i}' for i in reversed(range(13)))+'\n',
                          '  exact '+''.join(f'same{i}.trans (' for i in reversed(range(1,13)))+'same0'+')'*12+'\n')
    source+=f'''theorem complete_rows {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have link0 : assignment0 rho {copy} = assignment0 rho 0 := linked
'''
    for i,chunk in enumerate(chunks):
        source+=f'''  have current{i} : Satisfies (assignment{i+1} rho) {chunk}.rawRows := {chunk}.complete (assignment{i} rho) link{i}
  have link{i+1} : assignment{i+1} rho {copy} = assignment{i+1} rho 0 := by
    change {chunk}.completeAssignment (assignment{i} rho) {copy} = {chunk}.completeAssignment (assignment{i} rho) 0
    rw [{chunk}.preserves (assignment{i} rho) {copy} (by decide),{chunk}.preserves (assignment{i} rho) 0 (by decide),link{i}]
'''
        if i==0:source+='  have done0 := current0\n'
        else:
            source+=f'''  have previous{i} : Satisfies (assignment{i+1} rho) {chunk}.priorRows :=
    {chunk}.prior_preserved (assignment{i} rho) done{i-1}
  have done{i} : Satisfies (assignment{i+1} rho) ({chunk}.priorRows ++ {chunk}.rawRows) := by
    intro row member
    rcases List.mem_append.mp member with member | member
    · exact previous{i} row member
    · exact current{i} row member
'''
            # priorRows is right-associated; prove definitional agreement via append_assoc.
            source=source.replace(f'{chunk}.prior_preserved (assignment{i} rho) done{i-1}',
                f'{chunk}.prior_preserved (assignment{i} rho) (by simpa only ['+
                ','.join(p+'.priorRows' for p in chunks[1:i+1])+f',List.append_assoc] using done{i-1})')
    source+='  exact done12\n'
    if rows_only:
        for export in ('sound_coverage_checked','preserves','complete_rows'):source+=f'#print axioms {export}\n'
        return _signature_audits(source+f'end ShielddSecurity.{name}\n')
    source+=f'''theorem input_support_checked : {base}.inputs.all (fun terms => terms.all
    (fun term => decide (term.1 ∉ ownedWrites))) = true := by decide
theorem inputs_preserved {{F : Type}} [Field F] (rho : Nat → F) :
    {base}.inputs.map (eval (completeAssignment rho)) = {base}.inputs.map (eval rho) := by
  apply List.map_congr_left
  intro terms member
  apply eval_agrees
  intro term present
  exact preserves rho term.1 (of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp input_support_checked) terms member)) term present))
theorem complete_hash {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment rho) rawRows ∧
      eval (completeAssignment rho) {base}.output =
        Poseidon.hash{width} (Poseidon.castParameters {permutation}.parameters)
          {obj['hash']['domain']} ({base}.inputs.map (eval rho)) ∧
      (∀ column, column ∉ ownedWrites → completeAssignment rho column = rho column) := by
  have completed := complete_rows rho linked
  have soundRows : Satisfies (completeAssignment rho) {base}.rawRows := by
    intro row member
    exact completed row (of_decide_eq_true ((List.all_eq_true.mp sound_coverage_checked) row member))
  have one' : completeAssignment rho 0 = 1 := (preserves rho 0 (by decide)).trans one
  have meaning := {base}.actual_hash_sound (completeAssignment rho) one' soundRows
  rw [inputs_preserved rho] at meaning
  exact ⟨completed,meaning,preserves rho⟩
'''
    for export in ('sound_coverage_checked','preserves','complete_rows','input_support_checked','inputs_preserved','complete_hash'):
        source+=f'#print axioms {export}\n'
    return _signature_audits(source+f'end ShielddSecurity.{name}\n')
