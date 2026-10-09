"""Exact two-block NOTE commitment construction using captured original rows.

The block0 output is constructed before block1 absorbs it. Their actual shared
source LCs and all previous row supports are rechecked, never supplied as desired
output-value or row-satisfaction premises.
"""
from . import transfer_note_hash_join as joins,transfer_relation as relation
from . import generate_note_hash_block_completion as blocks
from .generate_hash_round import _signature_audits


def generate(page_data,extractions,note_data,accepted_roles,parameter_root,on_chunk=None,
             *,linear_declarations_per_module=None):
    checked=joins.inspect_calls(page_data,note_data,accepted_roles)
    if len(checked)!=2 or checked[0]['metadata']['role']!='commitment':
        raise relation.RelationError('two-block completion requires the exact NOTE15/8 commitment call')
    if not isinstance(extractions,(list,tuple)) or len(extractions)!=2:
        raise relation.RelationError('two-block completion exact row extraction inventory')
    obj=checked[0]['metadata'];base=f'RuntimeNoteHash{obj["slot"]}Commitment{obj["level"]}'
    for module,source in joins.generate(page_data,extractions,note_data,accepted_roles,parameter_root,
        linear_declarations_per_module=linear_declarations_per_module):yield module,source
    all_prior_support=set();all_owned=set();second_floor=None
    for block,(data,extracted) in enumerate(zip(page_data,extractions)):
        prefix=base+f'Block{block}';chunks=[];previous_support=set();owned=set();rows=set();expected=None
        context=blocks._context(data,extracted,note_data,accepted_roles,parameter_root)
        for index,start in enumerate(range(0,65,5)):
            plan=blocks._chunk_plan(context,start,min(start+5,65))
            writes=set(plan['writes'])
            if writes&(all_prior_support|all_owned|previous_support|owned):
                raise relation.RelationError('two-block completion later writes change prior actual row support')
            previous_support.update(c for row in plan['raw'].values() for terms in row for c,_ in terms)
            owned.update(writes);rows.update(plan['raw'])
            if expected is None:expected=set(plan['selected']['rows'])
            if on_chunk is not None:on_chunk(block,index,plan)
            module,source=blocks._chunk_source(prefix,index,plan,chunks);yield module,source;chunks.append(module)
        if rows!=expected:raise relation.RelationError('two-block completion full permutation row coverage')
        if block==1 and obj['constant_copy'] not in owned:
            floor=min(owned)
            if all(c==obj['constant_copy'] or c<floor for c in all_prior_support):second_floor=floor
        all_prior_support.update(previous_support);all_owned.update(owned)
        permutation=f'RuntimeHashBlock_spend{obj["slot"]}_commitment{obj["level"]}_permutation{block}_0'
        yield prefix+'Completion',blocks._composition(prefix,chunks,obj,rows_only=True,
            sound_module=prefix+'_Composition',sound_namespace=permutation)
    yield base+'Completion',_composition(base,obj,second_floor=second_floor)


def _composition(base,obj,*,second_floor=None,role_prefix='spend'):
    name=base+'Completion';first=base+'Block0Completion';second=base+'Block1Completion';copy=obj['constant_copy']
    permutation=f'RuntimeHashBlock_{role_prefix}{obj["slot"]}_{obj["role"]}{obj["level"]}_permutation'
    domain=obj['hash']['domain']
    source=f'''import ShielddSecurity.{base}
import ShielddSecurity.{first}
import ShielddSecurity.{second}
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact captured two-block NOTE15/8 call; full Transfer/native byte joins OPEN.
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := {first}.rawRows ++ {second}.rawRows
def ownedWrites : List Nat := {first}.ownedWrites ++ {second}.ownedWrites
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  {second}.completeAssignment ({first}.completeAssignment rho)
theorem prior_support_checked : {first}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ {second}.ownedWrites))) = true := by decide
theorem prior_preserved {{F : Type}} [Field F] (rho : Nat → F)
    (satisfied : Satisfies rho {first}.rawRows) : Satisfies ({second}.completeAssignment rho) {first}.rawRows := by
  intro row member
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval ({second}.completeAssignment rho) terms = eval rho terms := by
    apply eval_agrees
    intro term present
    exact {second}.preserves rho term.1 (of_decide_eq_true
      ((List.all_eq_true.mp ((List.all_eq_true.mp prior_support_checked) row member)) term (included term present)))
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact satisfied row member
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column := by
  have firstOutside : column ∉ {first}.ownedWrites := fun member => outside (List.mem_append_left _ member)
  have secondOutside : column ∉ {second}.ownedWrites := fun member => outside (List.mem_append_right _ member)
  exact ({second}.preserves ({first}.completeAssignment rho) column secondOutside).trans
    ({first}.preserves rho column firstOutside)
theorem sound_coverage_checked : {base}.rawRows.all (fun row => decide (row ∈ rawRows)) = true := by
  apply List.all_eq_true.mpr
  intro row member
  change row ∈ {permutation}0_0.rawRows ++
    {permutation}1_0.rawRows at member
  simp only [decide_eq_true_eq]
  rcases List.mem_append.mp member with member | member
  · exact List.mem_append.mpr (Or.inl (of_decide_eq_true
      ((List.all_eq_true.mp {first}.sound_coverage_checked) row member)))
  · exact List.mem_append.mpr (Or.inr (of_decide_eq_true
      ((List.all_eq_true.mp {second}.sound_coverage_checked) row member)))
theorem complete_rows {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment rho) rawRows := by
  have completed0 := {first}.complete_rows rho linked
  have linked1 : {first}.completeAssignment rho {copy} = {first}.completeAssignment rho 0 := by
    rw [{first}.preserves rho {copy} (by decide),{first}.preserves rho 0 (by decide),linked]
  have completed1 := {second}.complete_rows ({first}.completeAssignment rho) linked1
  have previous := prior_preserved ({first}.completeAssignment rho) completed0
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact previous row member
  · exact completed1 row member
theorem input_support_checked : {base}.inputs.all (fun terms => terms.all
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
    Satisfies (completeAssignment rho) rawRows ∧ eval (completeAssignment rho) {base}.output =
      Poseidon.hash6 (Poseidon.castParameters {permutation}0_0.parameters)
        {domain} ({base}.inputs.map (eval rho)) ∧
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
    if role_prefix!='spend':source=source.replace('Exact captured two-block NOTE15/8 call;',f'Exact captured two-block output {domain}/{len(obj["hash"]["inputs"])} call;')
    if second_floor is not None:
        source='import ShielddSecurity.ColumnFence\n'+source
        old=f'''theorem prior_support_checked : {first}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ {second}.ownedWrites))) = true := by decide'''
        new=f'''theorem prior_support_checked : {first}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ {second}.ownedWrites))) = true := by
  have lower : ColumnFence.checkWrites {copy} {second_floor} {second}.ownedWrites = true := by decide
  have upper : ColumnFence.checkRows {copy} {second_floor} {first}.rawRows = true := by decide
  have absent := ColumnFence.checked_rows {copy} {second_floor} {second}.ownedWrites {first}.rawRows lower upper
  apply List.all_eq_true.mpr
  intro row member
  apply List.all_eq_true.mpr
  intro term present
  simpa only [decide_eq_true_eq] using absent row member term present'''
        if source.count(old)!=1:raise relation.RelationError('two-block bounded prior source anchor')
        source=source.replace(old,new)
    for export in ('prior_support_checked','prior_preserved','preserves','sound_coverage_checked','complete_rows',
                   'input_support_checked','inputs_preserved','complete_hash'):source+=f'#print axioms {export}\n'
    return _signature_audits(source+f'end ShielddSecurity.{name}\n')
