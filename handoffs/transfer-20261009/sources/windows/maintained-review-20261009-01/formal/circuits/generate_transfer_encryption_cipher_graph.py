"""Join the physical detection/core assertions to the complete hash graph."""
import re

NAME = 'RuntimeTransferEncryptionFieldCipherGraph'
GRAPH = 'RuntimeTransferEncryptionHashGraph'
CIPHER = 'RuntimeEncryptionCipherRows'
CASES = [('detection0',6,'[(6,1)]'), ('detection1',7,f'{GRAPH}.output 0'),
         ('detection2',8,'[(108486,1)]'), ('detection3',9,'[]'),
         ('core0_confirmation',11,None), ('core0_amount',12,'[(4789,1)]'),
         ('core2_confirmation',14,None), ('core2_amount',15,'[(4789,1)]')]
SEEDS = [(0,12,10,8517), (1,17,16,8522), (2,15,13,8528), (3,21,20,8533)]


def generate(cipher_source):
    equations = {}
    for name, _, _ in CASES:
        pattern = (r'^theorem ' + name + r' \{F : Type\}.*?:\n'
                   r'    eval rho (\[.*?\]) = eval rho (\[.*?\]) := by$')
        found = re.search(pattern,cipher_source,re.M|re.S)
        assert found is not None, name
        equations[name] = found.groups()
    source = f'import ShielddSecurity.{GRAPH}\nimport ShielddSecurity.{CIPHER}\n'
    source += f'set_option maxHeartbeats 800000\nnamespace ShielddSecurity.{NAME}\n'
    source += f'def rawRows : List Row := {GRAPH}.rawRows ++ {CIPHER}.rawRows\n'
    source += f'def hashValue {{F : Type}} [Field F] (rho : Nat → F) (call : Nat) : F :=\n  {GRAPH}.hashAt call (({GRAPH}.inputs call).map (eval rho))\n'
    for name, _, _ in CASES:
        source += f'def {name} : Linear := {equations[name][0]}\n'
    for tier, stream, _, column in SEEDS:
        source += f'def seed{tier} {{F : Type}} [Field F] (rho : Nat → F) : F :=\n  eval rho (({GRAPH}.inputs {stream}).headD [])\n'
        source += f'def c2_{tier} : Linear := [({column},1)]\n'
    source += f'''variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
private theorem hash_rows (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho {GRAPH}.rawRows := by
  intro row inside
  exact satisfied row (List.mem_append_left _ inside)
private theorem cipher_rows (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho {CIPHER}.rawRows := by
  intro row inside
  exact satisfied row (List.mem_append_right _ inside)
private theorem hash_output (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) (call : Fin 24) :
    eval rho ({GRAPH}.output call.val) = hashValue rho call.val :=
  {GRAPH}.all_hashes_sound rho one (hash_rows rho satisfied) call
'''
    exports = []
    for name, call, plaintext in CASES:
        physical = equations[name][1]
        evaluated_plaintext = f'eval rho ({plaintext})'
        conclusion = f'hashValue rho {call}'
        if plaintext == f'{GRAPH}.output 0':
            conclusion = 'hashValue rho 0 + ' + conclusion
        elif plaintext not in (None,'[]'):
            conclusion = evaluated_plaintext + ' + ' + conclusion
        source += f'''theorem {name}_sound (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) : eval rho {name} = {conclusion} := by
  have physical := {CIPHER}.{name} rho (cipher_rows rho satisfied)
'''
        if plaintext is None:
            source += f'''  have same : eval rho {physical} = eval rho ({GRAPH}.output {call}) :=
    Compiler.canonical_equal rho _ _ (by decide)
  calc
    eval rho {name} = eval rho {physical} := physical
    _ = eval rho ({GRAPH}.output {call}) := same
    _ = hashValue rho {call} := hash_output rho one satisfied ⟨{call},by decide⟩
'''
        else:
            source += f'''  have same : eval rho {physical} = {evaluated_plaintext} + eval rho ({GRAPH}.output {call}) := by
    calc
      _ = eval rho ({plaintext} ++ {GRAPH}.output {call}) :=
        Compiler.canonical_equal rho _ _ (by decide)
      _ = _ := eval_append rho _ _
  have result : eval rho {name} = {evaluated_plaintext} + hashValue rho {call} := by
    calc
      eval rho {name} = eval rho {physical} := physical
      _ = {evaluated_plaintext} + eval rho ({GRAPH}.output {call}) := same
      _ = _ := by rw [hash_output rho one satisfied ⟨{call},by decide⟩]
'''
            if plaintext == f'{GRAPH}.output 0':
                source += '  rw [hash_output rho one satisfied ⟨0,by decide⟩] at result\n  exact result\n'
            elif plaintext == '[]':
                source += '  simpa only [eval,zero_add] using result\n'
            else:
                source += '  exact result\n'
        exports.append(name+'_sound')
    for tier, stream, secret, _ in SEEDS:
        source += f'''/-- The witness seed is recovered from the actual c2−secret input expression. -/
theorem c2_seed{tier}_sound (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows) :
    eval rho c2_{tier} = seed{tier} rho + hashValue rho {secret} := by
  have same : eval rho (({GRAPH}.inputs {stream}).headD []) =
      eval rho c2_{tier} - eval rho ({GRAPH}.output {secret}) := by
    calc
      _ = eval rho (Compiler.subtract c2_{tier} ({GRAPH}.output {secret})) :=
        Compiler.canonical_equal rho _ _ (by decide)
      _ = _ := Compiler.eval_subtract rho _ _
  rw [hash_output rho one satisfied ⟨{secret},by decide⟩] at same
  change seed{tier} rho = eval rho c2_{tier} - hashValue rho {secret} at same
  rw [same]
  ring
'''
        exports.append(f'c2_seed{tier}_sound')
    source += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n' for name in exports)
    source += f'end ShielddSecurity.{NAME}\n'
    assert len(exports) == 12 and not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source)
    return source, exports
