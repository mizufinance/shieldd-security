"""Construct24 actual quaternary routing/hash levels in their native order.

Only captured, checked product steps are assigned. A physical column fence is
verified against every prior actual row; it is not an allocator-order premise.
Encoded48bit positions and commitment construction are preceding stages. All
sources remain candidates until their exact kernel signatures/axioms pass.
"""
from pathlib import Path
from . import transfer_note_tree as tree,transfer_note_hash as hashes,transfer_relation as relation
from . import generate_note_tree_path as paths,generate_note_tree_completion as trees
from . import generate_note_hash_block_completion as blocks,transfer_note_hash_join as joins
from .generate_hash_round import linear,_signature_audits


def _read(page):
    if isinstance(page,bytes):return page
    if isinstance(page,Path):
        if page.stat().st_size>4*1024*1024:raise relation.RelationError('tree path bounded hash page')
        return page.read_bytes()
    raise relation.RelationError('tree path needs exact bytes or local page Path')


def level_plan(data,tree_extracted,page,hash_extracted,note_data,accepted_roles,parameter_root,slot,index,prior=()):
    slot=relation.natural(slot,2);index=relation.natural(index,24);page=_read(page)
    if (tree_extracted.get('slot'),tree_extracted.get('level'))!=(slot,index):
        raise relation.RelationError('tree completion exact routing role order')
    checked=tree.inspect_hash_link(data,page,note_data,accepted_roles)
    obj=hashes.inspect_boundaries(page,note_data,accepted_roles)['metadata']
    if (obj['slot'],obj['role'],obj['level'],obj['block'])!=(slot,'state',index,0):
        raise relation.RelationError('tree completion exact state page order')
    routing=trees.completion_plan(data,tree_extracted,note_data,accepted_roles)
    context=blocks._context(page,hash_extracted,note_data,accepted_roles,parameter_root)
    chunks=[];hash_writes=[];hash_rows={};previous_support=set()
    for start in range(0,65,5):
        chunk=blocks._chunk_plan(context,start,min(start+5,65))
        if set(chunk['writes'])&(set(hash_writes)|previous_support):
            raise relation.RelationError('tree hash later chunk changes prior actual rows')
        chunks.append(chunk);hash_writes.extend(chunk['writes']);hash_rows.update(chunk['raw'])
        previous_support.update(c for row in chunk['raw'].values() for terms in row for c,_ in terms)
    if set(hash_rows)!=set(context[0]['rows']):raise relation.RelationError('tree hash full65round coverage')
    copy=checked['metadata']['constant_copy'];writes=routing['writes']+hash_writes
    if len(set(writes))!=len(writes):raise relation.RelationError('tree routing/hash writes overlap')
    floor=min(writes);hash_floor=min(hash_writes)
    def below(rows,bound):return all(c==copy or c<bound for row in rows for terms in row for c,_ in terms)
    if copy in writes or not below(prior,floor):
        raise relation.RelationError('tree completion new writes do not preserve prior actual row fence')
    tree_rows=list(routing['selected']['raw'].values())
    if not below(tree_rows,hash_floor):raise relation.RelationError('tree hash writes do not preserve routing row fence')
    current=routing['current'];interfaces=[current['low'],current['high'],*current['siblings']]
    if index==0:interfaces.append(current['node'])
    if not below([(terms,()) for terms in interfaces],floor):
        raise relation.RelationError('tree completion shared/bit/sibling interface fence')
    return dict(slot=slot,index=index,copy=copy,floor=floor,hash_floor=hash_floor,writes=writes,
        routing=routing,chunks=chunks,context=context,checked=checked,page=page,
        raw=tree_rows+list(hash_rows.values()),interfaces=interfaces)


def generate(data,tree_extractions,pages,hash_extractions,note_data,accepted_roles,parameter_root,slot,
             *,linear_declarations_per_module=None,on_level=None):
    """Stream one accepted cone/dependency batch, discarding it before the next."""
    slot=relation.natural(slot,2);checked=tree.inspect_metadata(data,note_data,accepted_roles)
    for inventory in (tree_extractions,pages,hash_extractions):
        if not isinstance(inventory,(list,tuple)) or len(inventory)!=24:
            raise relation.RelationError('tree completion exact24 extraction/page inventory')
    prior=[];stages=[];floors=[]
    for index in range(24):
        plan=level_plan(data,tree_extractions[index],pages[index],hash_extractions[index],note_data,
            accepted_roles,parameter_root,slot,index,prior)
        for module,source in trees.generate(data,tree_extractions[index],note_data,accepted_roles):yield module,source
        page=plan['page'];base=f'RuntimeNoteHash{slot}State{index}'
        for module,source in joins.generate([page],[hash_extractions[index]],note_data,accepted_roles,parameter_root,
            linear_declarations_per_module=linear_declarations_per_module):yield module,source
        chunks=[]
        for n,chunk in enumerate(plan['chunks']):
            module,source=blocks._chunk_source(base,n,chunk,chunks);yield module,source;chunks.append(module)
        yield base+'Completion',blocks._composition(base,chunks,relation.record(page))
        module,source=_level_source(plan,stages);yield module,source;stages.append(module);floors.append(plan['floor'])
        if on_level is not None:on_level(index,plan)
        prior.extend(plan['raw'])
        del plan
    yield paths._join_source(checked,slot)
    yield _composition(checked,slot,stages,floors)


def _level_source(plan,previous):
    slot,index=plan['slot'],plan['index'];copy,floor=plan['copy'],plan['floor'];hash_floor=plan['hash_floor']
    t=f'RuntimeTransferNoteTree{slot}Level{index}';tc=t+'Completion'
    h=f'RuntimeNoteHash{slot}State{index}';hc=h+'Completion';name=t+'PathStage'
    imports=[tc,hc]+previous[-1:]
    source=''.join(f'import ShielddSecurity.{module}\n' for module in imports)+'import ShielddSecurity.ColumnFence\n'
    source+=f'''set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := {t}.rawRows ++ {hc}.rawRows
def priorRows : List Row := '''+(previous[-1]+'.priorRows ++ '+previous[-1]+'.rawRows' if previous else '[]')+'\n'
    source+=f'''def ownedWrites : List Nat := {tc}.ownedWrites ++ {hc}.ownedWrites
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  {hc}.completeAssignment ({tc}.completeAssignment rho)
theorem writes_checked : ColumnFence.checkWrites {copy} {floor} ownedWrites = true := by decide
theorem prior_checked : ColumnFence.checkRows {copy} {floor} priorRows = true := by decide
theorem hash_writes_checked : ColumnFence.checkWrites {copy} {hash_floor} {hc}.ownedWrites = true := by decide
theorem routing_checked : ColumnFence.checkRows {copy} {hash_floor} {t}.rawRows = true := by decide
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column := by
  have routing : column ∉ {tc}.ownedWrites := fun member => outside (List.mem_append.mpr (Or.inl member))
  have hashing : column ∉ {hc}.ownedWrites := fun member => outside (List.mem_append.mpr (Or.inr member))
  exact ({hc}.preserves ({tc}.completeAssignment rho) column hashing).trans ({tc}.preserves rho column routing)
theorem kept_value {{F : Type}} [Field F] (rho : Nat → F) (terms : Linear)
    (checked : terms.all (fun term => decide (term.1 = {copy} ∨ term.1 < {floor})) = true) :
    eval (completeAssignment rho) terms = eval rho terms := by
  apply eval_agrees
  intro term member
  exact preserves rho term.1 (ColumnFence.checked_column {copy} {floor} ownedWrites term.1 writes_checked
    (of_decide_eq_true ((List.all_eq_true.mp checked) term member)))
theorem prior_preserved {{F : Type}} [Field F] (rho : Nat → F) (satisfied : Satisfies rho priorRows) :
    Satisfies (completeAssignment rho) priorRows := by
  intro row member
  have outside := ColumnFence.checked_rows {copy} {floor} ownedWrites priorRows writes_checked prior_checked
  have left : eval (completeAssignment rho) row.a = eval rho row.a := by
    apply eval_agrees
    intro term present
    exact preserves rho term.1 (outside row member term (List.mem_append.mpr (Or.inl present)))
  have right : eval (completeAssignment rho) row.b = eval rho row.b := by
    apply eval_agrees
    intro term present
    exact preserves rho term.1 (outside row member term (List.mem_append.mpr (Or.inr present)))
  rw [left,right]
  exact satisfied row member
theorem complete_level {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0) (lo hi : Bool)
    (lowValue : eval rho {t}.low = Tree.bit lo) (highValue : eval rho {t}.high = Tree.bit hi) :
    Satisfies (completeAssignment rho) rawRows := by
  have routing := ({tc}.complete_level rho linked four lo hi lowValue highValue).1
  have linkHash : {tc}.completeAssignment rho {copy} = {tc}.completeAssignment rho 0 := by
    rw [{tc}.preserves rho {copy} (by decide),{tc}.preserves rho 0 (by decide),linked]
  have hashing := {hc}.complete_rows ({tc}.completeAssignment rho) linkHash
  have outside := ColumnFence.checked_rows {copy} {hash_floor} {hc}.ownedWrites {t}.rawRows
    hash_writes_checked routing_checked
  have retained : Satisfies (completeAssignment rho) {t}.rawRows := by
    intro row member
    have left : eval (completeAssignment rho) row.a = eval ({tc}.completeAssignment rho) row.a := by
      apply eval_agrees
      intro term present
      exact {hc}.preserves ({tc}.completeAssignment rho) term.1
        (outside row member term (List.mem_append.mpr (Or.inl present)))
    have right : eval (completeAssignment rho) row.b = eval ({tc}.completeAssignment rho) row.b := by
      apply eval_agrees
      intro term present
      exact {hc}.preserves ({tc}.completeAssignment rho) term.1
        (outside row member term (List.mem_append.mpr (Or.inr present)))
    rw [left,right]
    exact routing row member
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact retained row member
  · exact hashing row member
theorem sound_rows {{F : Type}} [Field F] (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho ({t}.rawRows ++ {h}.rawRows) := by
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact satisfied row (List.mem_append.mpr (Or.inl member))
  · exact satisfied row (List.mem_append.mpr (Or.inr (of_decide_eq_true
      ((List.all_eq_true.mp {hc}.sound_coverage_checked) row member))))
'''
    for export in ('writes_checked','prior_checked','hash_writes_checked','routing_checked','preserves','kept_value',
                   'prior_preserved','complete_level','sound_rows'):source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def _composition(checked,slot,stages,floors):
    sound=f'RuntimeTransferNoteTree{slot}Path';name=sound+'Completion';copy=checked['metadata']['constant_copy']
    source=f'import ShielddSecurity.{sound}\n'+''.join(f'import ShielddSecurity.{stage}\n' for stage in stages)
    source+=f'''set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := {stages[-1]}.priorRows ++ {stages[-1]}.rawRows
def levelWrites : Nat → List Nat := fun index => match index with
'''
    for i,stage in enumerate(stages):source+=f'  | {i} => {stage}.ownedWrites\n'
    source+='  | _ => []\ndef ownedWrites : List Nat := (List.range 24).flatMap levelWrites\n'
    source+='def assignment0 {F : Type} [Field F] (rho : Nat → F) : Nat → F := rho\n'
    for i,stage in enumerate(stages):source+=f'def assignment{i+1} {{F : Type}} [Field F] (rho : Nat → F) : Nat → F := {stage}.completeAssignment (assignment{i} rho)\n'
    source+='def completeAssignment {F : Type} [Field F] (rho : Nat → F) : Nat → F := assignment24 rho\n'
    source+='''theorem preserves {F : Type} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column := by
'''
    for i,stage in enumerate(stages):
        source+=f'''  have outside{i} : column ∉ {stage}.ownedWrites := by
    intro member
    exact outside (List.mem_flatMap.mpr ⟨{i},by decide,member⟩)
  have same{i} : assignment{i+1} rho column = assignment{i} rho column := {stage}.preserves (assignment{i} rho) column outside{i}
'''
    source+='  exact '+''.join(f'same{i}.trans (' for i in reversed(range(1,24)))+'same0'+')'*23+'\n'
    # Read-only LCs: initial commitment, position bits, and sibling witnesses.
    levels=checked['levels'][slot*24:(slot+1)*24]
    interfaces=[levels[0]['node']]+[terms for level in levels for terms in (level['low'],level['high'],*level['siblings'])]
    floor=min(floors)
    if any(c!=copy and c>=floor for terms in interfaces for c,_ in terms):
        raise relation.RelationError('tree completion whole path read-only interface fence')
    for bit in ('low','high'):
        source+=f'def {bit}Bits : Nat → Linear := fun index => match index with\n'
        for i in range(24):source+=f'  | {i} => RuntimeTransferNoteTree{slot}Level{i}.{bit}\n'
        source+='  | _ => []\n'
    source+='noncomputable def nativeSteps {F : Type} [Field F] (rho : Nat → F) (lo hi : Nat → Bool) : Nat → TreeBinding.Step F :=\n  fun index => match index with\n'
    for i in range(24):
        t=f'RuntimeTransferNoteTree{slot}Level{i}'
        source+=f'  | {i} => ⟨lo {i},hi {i},eval rho {t}.sibling0,eval rho {t}.sibling1,eval rho {t}.sibling2⟩\n'
    source+='  | _ => ⟨false,false,0,0,0⟩\n'
    source+='def interfaces : List Linear := ['+', '.join(linear(terms) for terms in interfaces)+']\n'
    source+=f'''theorem interfaces_checked : interfaces.all (fun terms => terms.all
    (fun term => decide (term.1 = {copy} ∨ term.1 < {floor}))) = true := by decide
theorem interface_preserved {{F : Type}} [Field F] (rho : Nat → F) (terms : Linear) (member : terms ∈ interfaces) :
    eval (completeAssignment rho) terms = eval rho terms := by
  have checked := (List.all_eq_true.mp interfaces_checked) terms member
'''
    # This avoids a121LC × ~10000ownedwrites membership certificate.
    for i,stage in enumerate(stages):
        source+=f'  have same{i} : eval (assignment{i+1} rho) terms = eval (assignment{i} rho) terms := {stage}.kept_value (assignment{i} rho) terms (by\n'
        source+='    apply List.all_eq_true.mpr\n    intro term present\n    have bound := of_decide_eq_true ((List.all_eq_true.mp checked) term present)\n    simp only [decide_eq_true_eq]\n    rcases bound with fixed | small\n    · exact Or.inl fixed\n    · exact Or.inr (Nat.lt_of_lt_of_le small (by decide)))\n'
    source+='  exact '+''.join(f'same{i}.trans (' for i in reversed(range(1,24)))+'same0'+')'*23+'\n'
    source+='''theorem complete_rows {F : Type} [Field F] [CharP F modulus] (rho : Nat → F)
'''
    source+=f'    (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0) (lo hi : Nat → Bool)\n'
    source+='    (lowValue : ∀ i < 24, eval rho (lowBits i) = Tree.bit (lo i))\n'
    source+='    (highValue : ∀ i < 24, eval rho (highBits i) = Tree.bit (hi i)) : Satisfies (completeAssignment rho) rawRows := by\n'
    source+=f'  have link0 : assignment0 rho {copy} = assignment0 rho 0 := linked\n'
    for i,stage in enumerate(stages):
        t=f'RuntimeTransferNoteTree{slot}Level{i}'
        # Earlier stages keep every later bit LC below their actual floors.
        for bit,condition in (('low','lowValue'),('high','highValue')):
            source+=f'  have {bit}{i} : eval (assignment{i} rho) {t}.{bit} = Tree.bit ({"lo" if bit=="low" else "hi"} {i}) := by\n'
            for n in range(i):source+=f'    have same{n} : eval (assignment{n+1} rho) {t}.{bit} = eval (assignment{n} rho) {t}.{bit} := {stages[n]}.kept_value (assignment{n} rho) {t}.{bit} (by decide)\n'
            if i:source+='    rw ['+','.join(f'same{n}' for n in reversed(range(i)))+']\n'
            source+=f'    exact {condition} {i} (by decide)\n'
        source+=f'''  have current{i} := {stage}.complete_level (assignment{i} rho) link{i} four (lo {i}) (hi {i}) low{i} high{i}
  have link{i+1} : assignment{i+1} rho {copy} = assignment{i+1} rho 0 := by
    change {stage}.completeAssignment (assignment{i} rho) {copy} = {stage}.completeAssignment (assignment{i} rho) 0
    rw [{stage}.preserves (assignment{i} rho) {copy} (by decide),{stage}.preserves (assignment{i} rho) 0 (by decide),link{i}]
'''
        if i==0:source+='  have done0 := current0\n'
        else:
            expansion=','.join(s+'.priorRows' for s in stages[1:i+1])
            source+=f'''  have previous{i} := {stage}.prior_preserved (assignment{i} rho)
    (by simpa only [{expansion},List.append_assoc] using done{i-1})
  have done{i} : Satisfies (assignment{i+1} rho) ({stage}.priorRows ++ {stage}.rawRows) := by
    intro row member
    rcases List.mem_append.mp member with member | member
    · exact previous{i} row member
    · exact current{i} row member
'''
    source+='  exact done23\n'
    source+=f'''theorem sound_rows {{F : Type}} [Field F] (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho {sound}.rawRows := by
  have localRows : ∀ i : Fin 24, Satisfies rho ({sound}.levelRows i.val) := by
    '''
    for i,stage in enumerate(stages):
        indent='    '+'  '*i
        source+='refine Fin.cases ?_ ?_\n'+indent+'· '
        source+=f'apply {stage}.sound_rows rho\n'+indent+'  intro row member\n'
        expression='List.mem_append.mpr (Or.inr member)'
        for _ in range(i+1,24):expression=f'List.mem_append.mpr (Or.inl ({expression}))'
        source+=indent+f'  exact satisfied row ({expression})\n'+indent+'· '
    source+='intro impossible; exact Fin.elim0 impossible\n'
    source+='  intro row member\n  obtain ⟨i,bound,present⟩ := List.mem_flatMap.mp member\n  exact localRows ⟨i,List.mem_range.mp bound⟩ row present\n'
    source+=f'''theorem steps_preserved {{F : Type}} [Field F] (rho : Nat → F) (lo hi : Nat → Bool)
    (lowValue : ∀ i < 24, eval rho (lowBits i) = Tree.bit (lo i))
    (highValue : ∀ i < 24, eval rho (highBits i) = Tree.bit (hi i)) :
    ∀ i : Fin 24, {sound}.steps (completeAssignment rho) i.val = nativeSteps rho lo hi i.val := by
  '''
    for i in range(24):
        indent='  '+'  '*i;t=f'RuntimeTransferNoteTree{slot}Level{i}'
        source+='refine Fin.cases ?_ ?_\n'+indent+'· '
        source+=f'change ⟨TreeTrace.bitOf (eval (completeAssignment rho) {t}.low),TreeTrace.bitOf (eval (completeAssignment rho) {t}.high),\n'
        source+=indent+f'    eval (completeAssignment rho) {t}.sibling0,eval (completeAssignment rho) {t}.sibling1,eval (completeAssignment rho) {t}.sibling2⟩ = _\n'
        for bit,condition,bits in (('low','lowValue','lowBits'),('high','highValue','highBits')):
            source+=indent+f'  have {bit} : eval rho {t}.{bit} = Tree.bit ({"lo" if bit=="low" else "hi"} {i}) := {condition} {i} (by decide)\n'
        source+=indent+'  rw ['+','.join(f'interface_preserved rho {t}.{term} (by decide)' for term in ('low','high','sibling0','sibling1','sibling2'))+']\n'
        source+=indent+'  rw [low,high,TreeTrace.bitOf_of_bit,TreeTrace.bitOf_of_bit]\n'+indent+'  rfl\n'+indent+'· '
    source+='intro impossible; exact Fin.elim0 impossible\n'
    source+=f'''theorem complete_path {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0) (lo hi : Nat → Bool)
    (lowValue : ∀ i < 24, eval rho (lowBits i) = Tree.bit (lo i))
    (highValue : ∀ i < 24, eval rho (highBits i) = Tree.bit (hi i)) :
    Satisfies (completeAssignment rho) rawRows ∧
      TreeBinding.root {sound}.rootHash 0 (eval rho ({sound}.nodes 0))
        ((List.range 24).map (nativeSteps rho lo hi)) = eval (completeAssignment rho) ({sound}.nodes 24) ∧
      (∀ column, column ∉ ownedWrites → completeAssignment rho column = rho column) := by
  have completed := complete_rows rho linked four lo hi lowValue highValue
  have actual := {sound}.actual_field_path (completeAssignment rho)
    ((preserves rho 0 (by decide)).trans one) four (sound_rows (completeAssignment rho) completed)
  have initial : eval (completeAssignment rho) ({sound}.nodes 0) = eval rho ({sound}.nodes 0) :=
    interface_preserved rho ({sound}.nodes 0) (by decide)
  have stepList : (List.range 24).map ({sound}.steps (completeAssignment rho)) =
      (List.range 24).map (nativeSteps rho lo hi) := by
    apply List.map_congr_left
    intro i member
    exact steps_preserved rho lo hi lowValue highValue ⟨i,List.mem_range.mp member⟩
  rw [initial,stepList] at actual
  exact ⟨completed,actual,preserves rho⟩
'''
    for export in ('preserves','interfaces_checked','interface_preserved','complete_rows','sound_rows','steps_preserved','complete_path'):source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
