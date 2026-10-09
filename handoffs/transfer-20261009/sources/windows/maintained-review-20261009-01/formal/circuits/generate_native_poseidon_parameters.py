"""Owned SDK coefficient-source join to the existing actual RNK parameter tables.

This is neither a row replay nor a Rust/compiler or cryptographic qualification.
Every coefficient is independently decoded from the pinned SDK artifact and
matched to the exact generated Int parameter expression, including sign.
"""
import hashlib
from pathlib import Path
import re
from .generate_hash_round import finite_function, signed
from .poseidon_graph import P, decode_json, parameters

NAMES = tuple(f'RuntimeHashBlock_authorization_rnk_permutation{i}_0' for i in range(3))


def _table(name, params, kind):
    render = (lambda n: str(signed(n))) if kind == 'Int' else str
    result = f'def {name} : Poseidon.Parameters {kind} {params["width"]} where\n  ark := fun index => match index with\n'
    for i, row in enumerate(params['ark']):
        result += f'    | {i} => '+finite_function(row, render, '0').replace('\n','\n    ')+'\n'
    result += '    | _ => fun _ => 0\n  mds := fun row => match row.val with\n'
    for i, row in enumerate(params['mds']):
        result += f'    | {i} => '+finite_function(row, render, '0').replace('\n','\n    ')+'\n'
    return result+'    | _ => fun _ => 0\n'


def _actual_section(path, namespace):
    """Only retain the bounded parameter section; never retain actual row lists."""
    section, started, seen_namespace = [], False, False
    with Path(path).open(encoding='utf-8') as stream:
        for line in stream:
            if line.strip() == f'namespace ShielddSecurity.{namespace}':
                seen_namespace = True
            if line.startswith('def parameters : Poseidon.Parameters Int '):
                if started:
                    raise ValueError('duplicate actual parameter definition')
                started = True
            if started and line.startswith('def states '):
                break
            if started:
                section.append(line)
                if sum(map(len, section)) > 100000:
                    raise ValueError('oversized actual parameter section')
    if not seen_namespace or not started:
        raise ValueError('actual parameter namespace/definition absent')
    return ''.join(section)


def _checked(path, width):
    obj = decode_json(Path(path).read_text(encoding='utf-8'))
    for key in ('alpha','full_rounds','partial_rounds','skip_matrices'):
        if type(obj.get(key)) is not int:
            raise ValueError('noninteger parameter recipe')
    for name in ('ark','mds'):
        if not isinstance(obj.get(name),list):
            raise ValueError('parameter matrix required')
        for row in obj[name]:
            if not isinstance(row,list) or any(not isinstance(x,str) or not re.fullmatch('[0-9a-f]{64}',x) for x in row):
                raise ValueError('canonical lowercase parameter bytes required')
    return parameters(Path(path),width)


def generate(parameter_root, actual_data_paths):
    root=Path(parameter_root)
    if len(actual_data_paths)!=3:
        raise ValueError('all three actual Data modules required')
    wide=_checked(root/'poseidon381-wide.json',6)
    small=_checked(root/'poseidon381.json',3)
    for i, path in enumerate(actual_data_paths):
        expected=_table('parameters',wide if i<2 else small,'Int')
        if _actual_section(path,NAMES[i]) != expected:
            raise ValueError(f'actual signed coefficient table mismatch block{i}')
    source=''.join(f'import ShielddSecurity.RuntimeRnkHash{i}_Data\n' for i in range(3))
    source+='import ShielddSecurity.ShielddNativePoseidonParameters\nset_option maxHeartbeats 1000000\n'
    source+='namespace ShielddSecurity.RuntimeNativePoseidonParameters\nopen ShielddNativePoseidonParameters\n'
    source+='''local instance finiteEntriesDecidable {n : Nat} (predicate : Fin n → Prop)
    [DecidablePred predicate] : Decidable (∀ i, predicate i) :=
  Fintype.decidableForallFintype
'''
    for label,params in [('wide',wide),('small',small)]:
        width=params['width']
        source+=_table(label+'Signed',params,'Int')+_table(label+'Canonical',params,'Nat')
        for table,height in [('ark',65),('mds',width)]:
            selector='r.val' if table=='ark' else 'r'
            source+=f'''theorem {label}_{table}_entries : ∀ (r : Fin {height}) (c : Fin {width}),
    {label}Canonical.{table} {selector} c < Scalar.modulus ∧
    Represents ({label}Signed.{table} {selector} c) ({label}Canonical.{table} {selector} c) := by
  unfold Represents
  decide
'''
        actual=NAMES[0 if width==6 else 2]
        source+=f'theorem {label}_parameters : {label}Signed = {actual}.parameters := rfl\n'
        for table,height in [('ark',65),('mds',width)]:
            selector='r.val' if table=='ark' else 'r'
            source+=f'''theorem {label}_{table}_bytes {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (r : Fin {height}) (c : Fin {width}) :
    ShielddNativeIvkHash.littleEndianWrite codec
      (({actual}.parameters.{table} {selector} c : Int) : F) =
      sourceBuffer ({label}Canonical.{table} {selector} c) := by
  rw [← {label}_parameters]
  exact coefficient_bytes codec _ _ ({label}_{table}_entries r c).1 ({label}_{table}_entries r c).2
'''
    source+='theorem wide_second_parameters : wideSigned = '+NAMES[1]+'.parameters := rfl\n'
    source+='theorem domain_ivs : 9*256+17 = (2321 : Nat) ∧ 1*256+18 = (274 : Nat) := by decide\n'
    audits=[label+'_'+suffix for label in ('wide','small') for suffix in ('ark_entries','mds_entries','parameters','ark_bytes','mds_bytes')]+['wide_second_parameters','domain_ivs']
    for name in audits:
        source+=f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n'
    source+='end ShielddSecurity.RuntimeNativePoseidonParameters\n'
    return {'source':source,'audits':audits,'coefficient_count':630,
            'scope':'exact SDK canonical ARK/MDS integers, signed actual parameter equality, finite byte-loader correspondence; source-only, no row/Rust/crypto qualification'}
