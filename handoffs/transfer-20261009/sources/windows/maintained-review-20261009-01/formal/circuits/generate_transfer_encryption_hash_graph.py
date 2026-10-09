"""Compose the 24 captured encryption hashes without a native-result premise.

Four six-call modules keep parameter conversion and call composition bounded.
The final module quantifies over every call of the same arbitrary assignment.
"""
import re

DOMAINS = [14]*5 + [12] + [10]*4 + [11,13,10,11,13,10,11,10,10,10,11,10,10,10]
GROUPS = [f'RuntimeTransferEncryptionHashGroup{i}' for i in range(4)]
WHOLE = 'RuntimeTransferEncryptionHashGraph'


def member(index):
    result = 'List.mem_cons.mpr (Or.inl rfl)'
    for _ in range(index):
        result = 'List.mem_cons.mpr (Or.inr (' + result + '))'
    return result


def audit(names):
    return ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n' for name in names)


def generate(records):
    assert len(records) == 24 and len(DOMAINS) == 24
    for call, record in enumerate(records):
        assert record['call'] == call and record['domain'] == DOMAINS[call]
        assert record['width'] == (6 if call in (5,11,14) else 3)
        assert record['parameter_body'] == records[5 if record['width'] == 6 else 0]['parameter_body']
    result = {}
    for group, name in enumerate(GROUPS):
        calls = records[group*6:(group+1)*6]
        source = 'import ShielddSecurity.Scalar\n'
        source += ''.join(f'import ShielddSecurity.{r["module"]}\n' for r in calls)
        if group:
            source += f'import ShielddSecurity.{GROUPS[0]}\n'
        source += f'set_option maxHeartbeats 800000\nnamespace ShielddSecurity.{name}\n'
        if group == 0:
            source += f'def smallRecipe : Poseidon.Parameters Int 3 := {records[0]["parameter_namespace"]}.parameters\n'
            source += f'def wideRecipe : Poseidon.Parameters Int 6 := {records[5]["parameter_namespace"]}.parameters\n'
        source += 'def rowPages : List (List Row) := [' + ','.join(r['module']+'.rawRows' for r in calls) + ']\n'
        source += 'def rawRows : List Row := rowPages.flatten\n'
        for definition in ('inputs','output'):
            ty = 'List Linear' if definition == 'inputs' else 'Linear'
            source += f'def {definition} (index : Nat) : {ty} := match index with\n'
            source += ''.join(f'  | {i} => {r["module"]}.{definition}\n' for i,r in enumerate(calls))
            source += '  | _ => []\n'
        source += 'def hashAt {F : Type} [Field F] (index : Nat) (values : List F) : F := match index with\n'
        recipes = []
        for i, r in enumerate(calls):
            recipe = 'wideRecipe' if r['width'] == 6 else 'smallRecipe'
            if group:
                recipe = GROUPS[0] + '.' + recipe
            recipes.append(recipe)
            source += f'  | {i} => Poseidon.hash{r["width"]} (Poseidon.castParameters {recipe}) {r["domain"]} values\n'
        source += '  | _ => 0\n'
        for i, r in enumerate(calls):
            source += f'theorem parameters_call{r["call"]} : {r["parameter_namespace"]}.parameters = {recipes[i]} := rfl\n'
        source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
theorem hashes_sound (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) (index : Fin 6) :
    eval rho (output index.val) = hashAt index.val ((inputs index.val).map (eval rho)) := by
  rcases index with ⟨index, bound⟩
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
'''
        for i,r in enumerate(calls):
            source += f'''  · have localRows : Satisfies rho {r['module']}.rawRows := by
      intro row inside
      apply satisfied row
      change row ∈ rowPages.flatten
      apply List.mem_flatten.mpr
      exact ⟨{r['module']}.rawRows,{member(i)},inside⟩
    have value := {r['module']}.actual_hash_sound rho one localRows
    rw [parameters_call{r['call']}] at value
    simpa only [output, inputs, hashAt] using value
'''
        source += audit([f'parameters_call{r["call"]}' for r in calls]+['hashes_sound'])
        source += f'end ShielddSecurity.{name}\n'
        result[name] = source

    source = ''.join(f'import ShielddSecurity.{name}\n' for name in GROUPS)
    source += f'set_option maxHeartbeats 400000\nnamespace ShielddSecurity.{WHOLE}\n'
    source += 'def rowPages : List (List Row) := [' + ','.join(name+'.rawRows' for name in GROUPS) + ']\n'
    source += 'def rawRows : List Row := rowPages.flatten\n'
    for definition in ('inputs','output'):
        ty = 'List Linear' if definition == 'inputs' else 'Linear'
        source += f'def group{definition.title()} (group index : Nat) : {ty} := match group with\n'
        source += ''.join(f'  | {i} => {name}.{definition} index\n' for i,name in enumerate(GROUPS))
        source += '  | _ => []\n'
    source += 'def groupHash {F : Type} [Field F] (group index : Nat) (values : List F) : F := match group with\n'
    source += ''.join(f'  | {i} => {name}.hashAt index values\n' for i,name in enumerate(GROUPS))
    source += '  | _ => 0\n'
    source += '''def inputs (call : Nat) : List Linear := groupInputs (call / 6) (call % 6)
def output (call : Nat) : Linear := groupOutput (call / 6) (call % 6)
def hashAt {F : Type} [Field F] (call : Nat) (values : List F) : F := groupHash (call / 6) (call % 6) values
variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem group_sound (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) (group : Fin 4) (index : Fin 6) :
    eval rho (groupOutput group.val index.val) = groupHash group.val index.val
      ((groupInputs group.val index.val).map (eval rho)) := by
  rcases group with ⟨group, bound⟩
  have choices : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl
'''
    for i,name in enumerate(GROUPS):
        source += f'''  · have localRows : Satisfies rho {name}.rawRows := by
      intro row inside
      apply satisfied row
      change row ∈ rowPages.flatten
      apply List.mem_flatten.mpr
      exact ⟨{name}.rawRows,{member(i)},inside⟩
    simpa only [groupOutput, groupInputs, groupHash] using {name}.hashes_sound rho one localRows index
'''
    source += '''/-- Every captured call uses its actual inputs, output, rows and shared recipe.
The native parameter loader, native input objects and callers are separate joins. -/
theorem all_hashes_sound (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) (call : Fin 24) :
    eval rho (output call.val) = hashAt call.val ((inputs call.val).map (eval rho)) := by
  exact group_sound rho one satisfied ⟨call.val / 6, by omega⟩
    ⟨call.val % 6, Nat.mod_lt _ (by decide)⟩
'''
    source += audit(['all_hashes_sound']) + f'end ShielddSecurity.{WHOLE}\n'
    result[WHOLE] = source
    for name, text in result.items():
        names = re.findall(r'^#check @([\w.]+)$',text,re.M)
        assert names == re.findall(r'^#print axioms ([\w.]+)$',text,re.M)
        assert len(names) == (1 if name == WHOLE else 7)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
    return result
