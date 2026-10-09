"""Actual note permutation certificates to complete native-framed hash calls.

Every block is reaccepted through closed source DAGs, independent Poseidon
parameters and actual ordinary rows. The generated join assumes only row
satisfaction, and imports separately audited bounded permutation modules.
"""
from . import transfer_note_hash as hashes,transfer_relation as relation
from .transfer_balance_rows import canonical,source_index
from .generate_hash_round import (generate_selected_block,split_block_modules,
                                  linear,_signature_audits)


def inspect_calls(page_data,note_data,accepted_roles):
    if not isinstance(page_data,(list,tuple)) or not 1<=len(page_data)<=2:
        raise relation.RelationError('complete note call requires one or two pages')
    checked=[hashes.inspect_boundaries(data,note_data,accepted_roles) for data in page_data]
    first=checked[0]['metadata'];count=2 if first['role']=='commitment' else 1
    if len(checked)!=count or [c['metadata']['block'] for c in checked]!=list(range(count)):
        raise relation.RelationError('complete note call missing/reordered blocks')
    shared={}
    for part in checked:
        obj=part['metadata']
        if (any(obj[k]!=first[k] for k in ('relation_digest','domain_size','full_rows','constant_copy','slot','role','level'))
            or obj['hash']!=first['hash']):
            raise relation.RelationError('complete note call actual source boundaries mismatch')
        for handle,lc in part['observed'].items():
            if handle in shared and shared[handle]!=lc:
                raise relation.RelationError('complete note call shared compiler LC mismatch')
            shared[handle]=lc
    return checked


def generate(page_data,extractions,note_data,accepted_roles,parameter_root,rounds_per_module=5,
             *,linear_declarations_per_module=None):
    """Return dependency-ordered source modules; no generated hand edits needed."""
    checked=inspect_calls(page_data,note_data,accepted_roles)
    if not isinstance(extractions,(list,tuple)) or len(extractions)!=len(checked):
        raise relation.RelationError('complete note call row extraction inventory')
    selections=[hashes.round_selection(data,extracted,note_data,accepted_roles,parameter_root)
        for data,extracted in zip(page_data,extractions)]
    obj=checked[0]['metadata'];base=f'RuntimeNoteHash{obj["slot"]}{obj["role"].capitalize()}{obj["level"]}'
    return _generate_checked(checked,selections,base,rounds_per_module,
        linear_declarations_per_module=linear_declarations_per_module)


def _generate_checked(checked,selections,base,rounds_per_module=5,*,linear_declarations_per_module=None,width=6):
    """Algebra emitter after the owning typed ingress accepts each page."""
    if width not in (3,6) or len(checked)!=len(selections) or not 1<=len(checked)<=2:
        raise relation.RelationError('checked hash emitter exact block inventory')
    obj=checked[0]['metadata'];arity=len(obj['hash']['inputs']);domain=obj['hash']['domain']
    sources=[];permutations=[]
    for index,(part,selected) in enumerate(zip(checked,selections)):
        if selected['calls'][0]['parameters']['width']!=width:
            raise relation.RelationError('hash emitter width mismatch')
        role=selected['calls'][0]['role']
        body=generate_selected_block(part['metadata'],selected,role,0,part['metadata_sha256'],permutation_only=True)
        prefix=base+f'Block{index}'
        sources.extend(split_block_modules(body,prefix,rounds_per_module,
            linear_declarations_per_module=linear_declarations_per_module))
        permutations.append('RuntimeHashBlock_'+role.replace('.','_')+'_0')
    # Use accepted source inputs/output, not the permutation-only graph's cone
    # boundary list: absorbed state0 is NOT the original native hash input list.
    observed=checked[0]['observed']
    def value(ref):
        return observed[source_index(ref['source'])] if 'source' in ref else canonical([(0,int(ref['native'],16))])
    inputs=[value(ref) for ref in obj['hash']['inputs']]
    output=value(obj['hash']['output'])
    source=''.join(f'import ShielddSecurity.{base}Block{i}_Composition\n' for i in range(len(checked)))
    source+=f'''set_option maxHeartbeats 800000
namespace ShielddSecurity.{base}
-- Complete captured note call only; relation {obj['relation_digest']}.
-- Row/DAG/parameter correspondence rechecked by maintained generator.
-- Whole Transfer, native byte interpretation and hash security remain OPEN.
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := '''+' ++ '.join(p+'.rawRows' for p in permutations)+'\n'
    source+='def inputs : List Linear := ['+', '.join(linear(lc) for lc in inputs)+']\n'
    source+=f'def output : Linear := {linear(output)}\n'
    for i,permutation in enumerate(permutations):
        before=f'Poseidon.initialLinear {domain} {arity}' if i==0 else permutations[i-1]+'.states 65'
        source+=f'def before{i} : Poseidon.State Linear {width} := {before}\n'
        source+=f'def inputs{i} : List Linear := ['+', '.join(linear(lc) for lc in inputs[(width-1)*i:(width-1)*(i+1)])+']\n'
        source+=f'''theorem absorption{i} : ∀ column : Fin {width},
    Compiler.canonical modulus ({permutation}.states 0 column) =
      Compiler.canonical modulus (Poseidon.absorbLinear before{i} inputs{i} column) := by decide
theorem block{i}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho {permutation}.rawRows) :
    (fun column => eval rho ({permutation}.states 65 column)) =
      Poseidon.permute (Poseidon.castParameters {permutation}.parameters)
        (Poseidon.absorb (fun column => eval rho (before{i} column)) (inputs{i}.map (eval rho))) := by
  have boundary : (fun column => eval rho ({permutation}.states 0 column)) =
      Poseidon.absorb (fun column => eval rho (before{i} column)) (inputs{i}.map (eval rho)) := by
    calc
      _ = (fun column => eval rho (Poseidon.absorbLinear before{i} inputs{i} column)) := by
        funext column
        exact Compiler.canonical_equal rho _ _ (absorption{i} column)
      _ = _ := Poseidon.eval_absorbLinear rho before{i} inputs{i}
  simpa only [boundary] using {permutation}.permutation_sound rho one satisfied
'''
    source+=f'''theorem actual_hash_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho output = Poseidon.hash{width} (Poseidon.castParameters {permutations[0]}.parameters)
      {domain} (inputs.map (eval rho)) := by
'''
    for i,permutation in enumerate(permutations):
        if len(checked)==1:source+=f'  have rows{i} : Satisfies rho {permutation}.rawRows := satisfied\n'
        else:
            side='inl' if i==0 else 'inr'
            source+=f'''  have rows{i} : Satisfies rho {permutation}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.{side} member))
'''
        source+=f'  have block{i} := block{i}_sound rho one rows{i}\n'
    source+=f'''  have initial_value : (fun column => eval rho (before0 column)) = Poseidon.initial {domain} {arity} :=
    Poseidon.eval_initialLinear rho one {domain} {arity}
  rw [initial_value] at block0
'''
    if len(checked)==2:
        source+=f'''  have parameters_equal : {permutations[1]}.parameters = {permutations[0]}.parameters := rfl
  rw [parameters_equal] at block1
  change (fun column => eval rho ({permutations[1]}.states 65 column)) =
    Poseidon.permute (Poseidon.castParameters {permutations[0]}.parameters)
      (Poseidon.absorb (fun column => eval rho ({permutations[0]}.states 65 column)) (inputs1.map (eval rho))) at block1
  rw [block0] at block1
'''
    last=len(checked)-1
    source+=f'''  have coordinate := congrArg (fun state : Poseidon.State F {width} => state ⟨1,by decide⟩) block{last}
  dsimp only at coordinate
  have output_equal : eval rho output = eval rho ({permutations[last]}.states 65 ⟨1,by decide⟩) :=
    Compiler.canonical_equal rho _ _ (by decide)
  rw [← output_equal] at coordinate
  simpa only [Poseidon.hash{width},inputs,inputs0,'''+('inputs1,' if last else '')+f'''
    List.map_cons,List.map_nil,List.length_cons,List.length_nil,Poseidon.chunks{width-1},
    Poseidon.sponge,List.foldl_cons,List.foldl_nil] using coordinate
'''
    for i in range(len(checked)):
        source+=f'#print axioms absorption{i}\n#print axioms block{i}_sound\n'
    source+=f'#print axioms actual_hash_sound\nend ShielddSecurity.{base}\n'
    sources.append((base,_signature_audits(source)))
    return sources
