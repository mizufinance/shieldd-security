"""Stream actual24level wiring/hash dependencies then a symbolic path join.

All actual row and closed permutation checks remain mandatory. Yielded modules
are unqualified candidates; callers retain exact source/dependency hashes and
kernel-check them in order. Native position/byte interpretation remains open.
"""
from . import transfer_note_tree as tree,transfer_note_hash as hashes,transfer_note_hash_join as joins
from . import transfer_relation as relation
from .generate_hash_round import linear,_signature_audits


def inspect_pages(data,pages,note_data,accepted_roles,slot):
    slot=relation.natural(slot,2);checked=tree.inspect_metadata(data,note_data,accepted_roles)
    if not isinstance(pages,(list,tuple)) or len(pages)!=24:
        raise relation.RelationError('actual note path needs exactly24 state pages')
    for index,page in enumerate(pages):
        obj=hashes.inspect_boundaries(page,note_data,accepted_roles)['metadata']
        if (obj['slot'],obj['role'],obj['level'],obj['block'])!=(slot,'state',index,0):
            raise relation.RelationError('actual note path exact state page order')
        tree.inspect_hash_link(data,page,note_data,accepted_roles)
    return checked


def generate(data,tree_extractions,pages,hash_extractions,note_data,accepted_roles,parameter_root,slot):
    """Yield one bounded dependency batch at a time, never all24 source cones."""
    checked=inspect_pages(data,pages,note_data,accepted_roles,slot)
    if (not isinstance(tree_extractions,(list,tuple)) or not isinstance(hash_extractions,(list,tuple)) or
        len(tree_extractions)!=24 or len(hash_extractions)!=24):
        raise relation.RelationError('actual path exact tree/hash row extraction inventory')
    for index,page in enumerate(pages):
        extracted=tree_extractions[index]
        if (extracted.get('slot'),extracted.get('level'))!=(slot,index):
            raise relation.RelationError('actual path wiring extraction role order')
        name=f'RuntimeTransferNoteTree{slot}Level{index}'
        yield name,tree.generate_level(data,extracted,note_data,accepted_roles)
        for module,source in joins.generate([page],[hash_extractions[index]],note_data,accepted_roles,parameter_root):
            yield module,source
    yield _join_source(checked,slot)


def _join_source(checked,slot):
    """Join previously emitted, exact per-level row/hash modules symbolically."""
    levels=checked['metadata']['levels'][slot*24:(slot+1)*24]
    observed=checked['observed'];value=lambda ref:observed[tuple(ref['source'])]
    name=f'RuntimeTransferNoteTree{slot}Path'
    source='import ShielddSecurity.TreeTrace\n'
    for i in range(24):
        source+=f'import ShielddSecurity.RuntimeTransferNoteTree{slot}Level{i}\n'
        source+=f'import ShielddSecurity.RuntimeNoteHash{slot}State{i}\n'
    source+=f'''set_option maxHeartbeats 800000
namespace ShielddSecurity.{name}
-- Actual field path only; relation {checked['metadata']['relation_digest']}.
-- Native48bit position/byte interpretation and whole Transfer remain OPEN.
def modulus : Nat := {relation.MODULUS}
def levelRows : Nat → List Row := fun index => match index with
'''
    for i in range(24):source+=f'  | {i} => RuntimeTransferNoteTree{slot}Level{i}.rawRows ++ RuntimeNoteHash{slot}State{i}.rawRows\n'
    source+='  | _ => []\ndef rawRows : List Row := (List.range 24).flatMap levelRows\n'
    source+='def nodes : Nat → Linear := fun index => match index with\n'
    source+=f'  | 0 => {linear(value(levels[0]["node"]))}\n'
    for i,level in enumerate(levels):source+=f'  | {i+1} => {linear(value(level["output"]))}\n'
    source+='  | _ => []\nnoncomputable def steps {F : Type} [Field F] (rho : Nat → F) : Nat → TreeBinding.Step F :=\n  fun index => match index with\n'
    for i in range(24):
        t=f'RuntimeTransferNoteTree{slot}Level{i}'
        source+=f'  | {i} => ⟨TreeTrace.bitOf (eval rho {t}.low),TreeTrace.bitOf (eval rho {t}.high),eval rho {t}.sibling0,eval rho {t}.sibling1,eval rho {t}.sibling2⟩\n'
    source+='  | _ => ⟨false,false,0,0,0⟩\n'
    p0=f'RuntimeHashBlock_spend{slot}_state0_permutation0_0'
    source+=f'''def rootHash {{F : Type}} [Field F] : Nat → List F → F := fun level children =>
  Poseidon.hash6 (Poseidon.castParameters {p0}.parameters) 1 (((level+1 : Nat) : F)::children)
theorem level_rows {{F : Type}} [Field F] (rho : Nat → F) (satisfied : Satisfies rho rawRows)
    (index : Nat) (bound : index < 24) : Satisfies rho (levelRows index) := by
  intro row member
  exact satisfied row (List.mem_flatMap.mpr ⟨index,List.mem_range.mpr bound,member⟩)
'''
    for i in range(24):
        t=f'RuntimeTransferNoteTree{slot}Level{i}';h=f'RuntimeNoteHash{slot}State{i}'
        pi=f'RuntimeHashBlock_spend{slot}_state{i}_permutation0_0'
        source+=f'''theorem step{i}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho (nodes {i+1}) = rootHash {i} (Tree.children (steps rho {i}).low (steps rho {i}).high
      (eval rho (nodes {i})) (steps rho {i}).first (steps rho {i}).second (steps rho {i}).third) := by
  have localRows : Satisfies rho ({t}.rawRows ++ {h}.rawRows) := level_rows rho satisfied {i} (by decide)
  have treeRows : Satisfies rho {t}.rawRows := by
    intro row member
    exact localRows row (List.mem_append.mpr (Or.inl member))
  have hashRows : Satisfies rho {h}.rawRows := by
    intro row member
    exact localRows row (List.mem_append.mpr (Or.inr member))
  obtain ⟨lo,hi,hlo,hhi,children⟩ := {t}.ordered_children rho four treeRows
  have low : TreeTrace.bitOf (eval rho {t}.low) = lo := by
    rw [← hlo]
    exact TreeTrace.bitOf_of_bit lo
  have high : TreeTrace.bitOf (eval rho {t}.high) = hi := by
    rw [← hhi]
    exact TreeTrace.bitOf_of_bit hi
  have childrenEq : [eval rho {t}.child0,eval rho {t}.child1,eval rho {t}.child2,eval rho {t}.child3] =
      Tree.children (steps rho {i}).low (steps rho {i}).high (eval rho (nodes {i}))
        (steps rho {i}).first (steps rho {i}).second (steps rho {i}).third := by
    change _ = Tree.children (TreeTrace.bitOf (eval rho {t}.low)) (TreeTrace.bitOf (eval rho {t}.high))
      (eval rho {t}.node) (eval rho {t}.sibling0) (eval rho {t}.sibling1) (eval rho {t}.sibling2)
    rw [low,high]
    exact children
  have inputsEq : {h}.inputs.map (eval rho) = (({i+1} : Nat) : F)::
      [eval rho {t}.child0,eval rho {t}.child1,eval rho {t}.child2,eval rho {t}.child3] := by
    change eval rho [(0,{i+1})] :: [eval rho {t}.child0,eval rho {t}.child1,eval rho {t}.child2,eval rho {t}.child3] = _
    simp only [eval,Int.cast_ofNat,Int.cast_one,one,mul_one,add_zero]
  have hashed := {h}.actual_hash_sound rho one hashRows
'''
        if i:source+=f'  have parameterEqual : {pi}.parameters = {p0}.parameters := rfl\n  rw [parameterEqual] at hashed\n'
        source+=f'''  change eval rho (nodes {i+1}) = _ at hashed
  rw [inputsEq,childrenEq] at hashed
  exact hashed
'''
    source+='''theorem actual_field_path {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    TreeBinding.root rootHash 0 (eval rho (nodes 0)) ((List.range 24).map (steps rho)) = eval rho (nodes 24) := by
  have transitions : ∀ index : Fin 24, eval rho (nodes (index.val+1)) =
      rootHash index.val (Tree.children (steps rho index.val).low (steps rho index.val).high
        (eval rho (nodes index.val)) (steps rho index.val).first (steps rho index.val).second (steps rho index.val).third) := by
    '''
    for i in range(24):
        indent='    '+'  '*i
        source+='refine Fin.cases ?_ ?_\n'+indent+f'· exact step{i}_sound rho one four satisfied\n'+indent+'· '
    source+='intro impossible; exact Fin.elim0 impossible\n'
    source+='''  exact TreeTrace.sequence_root rootHash 0 24 (fun index => eval rho (nodes index)) (steps rho)
    (fun index bound => by simpa only [Nat.zero_add] using transitions ⟨index,bound⟩)
#print axioms level_rows
'''
    for i in range(24):source+=f'#print axioms step{i}_sound\n'
    source+=f'#print axioms actual_field_path\nend ShielddSecurity.{name}\n'
    return name,_signature_audits(source)
