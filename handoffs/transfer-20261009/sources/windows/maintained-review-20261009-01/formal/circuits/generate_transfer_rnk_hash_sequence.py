"""Compose the three retained RNK hash constructors without another graph.

This source consumer checks their finite write/support layout. Qualification
of the input sources and recursive proof dependencies remains a root-owned
receipt check. The new theorem constructs rows without component satisfaction
premises; native arguments and registered-leaf source association are separate.
"""
import ast
import re
from .transfer_relation import RelationError
from .generate_hash_round import _signature_audits


def inspect_sources(sources):
    try:
        return _inspect_sources(sources)
    except (KeyError, TypeError, IndexError, AttributeError, ValueError, UnicodeError) as error:
        raise RelationError('RNK hash typed retained source closure') from error


def _inspect_sources(sources):
    expected = {f'RuntimeTransferRnkHash{block}OwnedCompletion' for block in range(3)}
    expected |= {f'RuntimeTransferRnkHash{block}OwnedCompletionChunk{chunk}'
                 for block in range(3) for chunk in range(13)}
    if not isinstance(sources, dict) or set(sources) != expected:
        raise RelationError('RNK hash exact three constructors and39 bounded chunks')
    ranges = [(60778, 61193), (61194, 61613), (61614, 61929)]
    result = []
    for block, (lower, upper) in enumerate(ranges):
        chunks = []; owned = []; support = set()
        stem = f'RuntimeTransferRnkHash{block}OwnedCompletion'
        for chunk in range(13):
            name = stem+f'Chunk{chunk}'; source = sources[name]
            if not isinstance(source, bytes) or len(source) > 2**20:
                raise RelationError('RNK hash bounded retained source bytes')
            try: text = source.decode('utf8')
            except UnicodeError as error: raise RelationError('RNK hash source encoding') from error
            if (text.count('namespace ShielddSecurity.'+name+'\n') != 1 or
                not text.rstrip().endswith('end ShielddSecurity.'+name)):
                raise RelationError('RNK hash exact retained chunk namespace')
            matches = re.findall(r'^def ownedWrites : List Nat := (\[[^\n]*\])$', text, re.M)
            if len(matches) != 1 or text.count('def rawRows : List Row := [\n') != 1:
                raise RelationError('RNK hash exact finite write/row declarations')
            writes = ast.literal_eval(matches[0])
            if (not isinstance(writes, list) or not writes or any(type(value) is not int for value in writes)
                or len(writes) != len(set(writes)) or any(not lower <= value <= upper for value in writes)):
                raise RelationError('RNK hash actual owned write interval')
            remainder = text.split('def rawRows : List Row := [\n', 1)[1]
            if remainder.count('\ndef priorRows : List Row :=') != 1:
                raise RelationError('RNK hash exact raw-row declaration boundary')
            body = remainder.split('\ndef priorRows : List Row :=', 1)[0].rstrip()
            if not body.endswith(']'):
                raise RelationError('RNK hash closed actual row declaration')
            body = body[:-1]
            rows = body.count('⟨')
            if not 0 < rows <= 512:
                raise RelationError('RNK hash bounded actual row chunk')
            columns = {int(value) for value in re.findall(r'\(([0-9]+),\s*\(', body)}
            if not columns or any(value > upper and value != 200692 for value in columns):
                raise RelationError('RNK hash original row support fence')
            chunks.append(dict(name=name, writes=writes, rows=rows, support=sorted(columns)))
            owned.extend(writes); support |= columns
        # These are finite support fences, not compiler-origin assumptions.
        if sorted(owned) != list(range(lower, upper+1)):
            raise RelationError('RNK hash complete disjoint actual write range')
        source = sources[stem]
        if not isinstance(source, bytes) or len(source) > 2**20:
            raise RelationError('RNK hash retained composition bytes')
        text = source.decode('utf8')
        imports = re.findall(r'^import ShielddSecurity\.([A-Za-z0-9_]+)$', text, re.M)
        if (text.count('namespace ShielddSecurity.'+stem+'\n') != 1 or
            not text.rstrip().endswith('end ShielddSecurity.'+stem) or
            imports != [f'RuntimeRnkHash{block}_Data', *(item['name'] for item in chunks)] or any(
                text.count('theorem '+name+' ') != 1 for name in ('preserves', 'complete_rows'))):
            raise RelationError('RNK hash exact constructor import/API closure')
        result.append(dict(name=stem, lower=lower, upper=upper, chunks=chunks, support=sorted(support)))
    return result


def generate(sources):
    parts = inspect_sources(sources)
    name = 'RuntimeRnkHashSequenceCompletion'
    source = 'import ShielddSecurity.Scalar\n'
    source += ''.join('import ShielddSecurity.'+part['name']+'\n' for part in parts)
    source += 'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
    source += f'namespace ShielddSecurity.{name}\n'
    for index, part in enumerate(parts):
        stem = part['name']
        source += f'''private theorem writes{index}_bound : ∀ column ∈ {stem}.ownedWrites,
    {part['lower']} ≤ column ∧ column ≤ {part['upper']} := by
  have checked : {stem}.ownedWrites.all (fun column => decide
    ({part['lower']} ≤ column ∧ column ≤ {part['upper']})) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
'''
        for chunk, info in enumerate(part['chunks']):
            source += f'''private theorem support{index}_{chunk} : ∀ row ∈ {info['name']}.rawRows,
    ∀ term ∈ row.a ++ row.b, term.1 ≤ {part['upper']} ∨ term.1 = 200692 := by
  have checked : {info['name']}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ≤ {part['upper']} ∨ term.1 = 200692))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
'''
        chain=part['chunks'][0]['name']+'.rawRows'
        for info in part['chunks'][1:]:chain='('+chain+' ++ '+info['name']+'.rawRows)'
        source += f'''private theorem support{index} : ∀ row ∈ {stem}.rawRows,
    ∀ term ∈ row.a ++ row.b, term.1 ≤ {part['upper']} ∨ term.1 = 200692 := by
  intro row member term present
  change row ∈ '''+chain+''' at member
'''
        def dispatch(chunk,member,indent):
            if chunk==0:return indent+f'exact support{index}_0 row {member} term present\n'
            earlier=f'earlier{chunk}'
            return (indent+f'rcases List.mem_append.mp {member} with {earlier} | last{chunk}\n'+
                indent+'· '+dispatch(chunk-1,earlier,indent+'  ').lstrip()+
                indent+f'· exact support{index}_{chunk} row last{chunk} term present\n')
        source+=dispatch(12,'member','  ')
    source += '''variable {F : Type} [Field F] [CharP F Scalar.modulus]
def assignment1 (base : Nat → F) : Nat → F := RuntimeTransferRnkHash0OwnedCompletion.completeAssignment base
def assignment2 (base : Nat → F) : Nat → F := RuntimeTransferRnkHash1OwnedCompletion.completeAssignment (assignment1 base)
def completed (base : Nat → F) : Nat → F := RuntimeTransferRnkHash2OwnedCompletion.completeAssignment (assignment2 base)
def originalRows : List Row := (RuntimeTransferRnkHash0OwnedCompletion.rawRows ++
  RuntimeTransferRnkHash1OwnedCompletion.rawRows) ++ RuntimeTransferRnkHash2OwnedCompletion.rawRows
theorem preserves (base : Nat → F) (column : Nat)
    (outside : column < 60778 ∨ 61929 < column) : completed base column = base column := by
  have excluded0 : column ∉ RuntimeTransferRnkHash0OwnedCompletion.ownedWrites := by
    intro member; have bounds := writes0_bound column member; omega
  have excluded1 : column ∉ RuntimeTransferRnkHash1OwnedCompletion.ownedWrites := by
    intro member; have bounds := writes1_bound column member; omega
  have excluded2 : column ∉ RuntimeTransferRnkHash2OwnedCompletion.ownedWrites := by
    intro member; have bounds := writes2_bound column member; omega
  exact (RuntimeTransferRnkHash2OwnedCompletion.preserves _ column excluded2).trans
    ((RuntimeTransferRnkHash1OwnedCompletion.preserves _ column excluded1).trans
      (RuntimeTransferRnkHash0OwnedCompletion.preserves base column excluded0))
theorem eval_preserved (base : Nat → F) (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 < 60778 ∨ 61929 < term.1) :
    eval (completed base) terms = eval base terms :=
  eval_agrees _ _ terms (by intro term member; exact preserves base term.1 (outside term member))
theorem complete_rows (base : Nat → F) (linked : base 200692 = base 0) :
    Satisfies (completed base) originalRows := by
  have link1 : assignment1 base 200692 = assignment1 base 0 := by
    change RuntimeTransferRnkHash0OwnedCompletion.completeAssignment base 200692 =
      RuntimeTransferRnkHash0OwnedCompletion.completeAssignment base 0
    rw [RuntimeTransferRnkHash0OwnedCompletion.preserves base 200692 (by
      intro member; have bounds := writes0_bound 200692 member; omega),
      RuntimeTransferRnkHash0OwnedCompletion.preserves base 0 (by
      intro member; have bounds := writes0_bound 0 member; omega),linked]
  have link2 : assignment2 base 200692 = assignment2 base 0 := by
    change RuntimeTransferRnkHash1OwnedCompletion.completeAssignment (assignment1 base) 200692 =
      RuntimeTransferRnkHash1OwnedCompletion.completeAssignment (assignment1 base) 0
    rw [RuntimeTransferRnkHash1OwnedCompletion.preserves _ 200692 (by
      intro member; have bounds := writes1_bound 200692 member; omega),
      RuntimeTransferRnkHash1OwnedCompletion.preserves _ 0 (by
      intro member; have bounds := writes1_bound 0 member; omega),link1]
  have done0 := RuntimeTransferRnkHash0OwnedCompletion.complete_rows base linked
  have done1 := RuntimeTransferRnkHash1OwnedCompletion.complete_rows (assignment1 base) link1
  have done2 := RuntimeTransferRnkHash2OwnedCompletion.complete_rows (assignment2 base) link2
  have previous0 : Satisfies (completed base) RuntimeTransferRnkHash0OwnedCompletion.rawRows := by
    intro row member
    have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval (completed base) terms = eval (assignment1 base) terms := by
      apply eval_agrees
      intro term present
      have supported := support0 row member term (inside term present)
      have not1 : term.1 ∉ RuntimeTransferRnkHash1OwnedCompletion.ownedWrites := by
        intro written; have bounds := writes1_bound term.1 written; omega
      have not2 : term.1 ∉ RuntimeTransferRnkHash2OwnedCompletion.ownedWrites := by
        intro written; have bounds := writes2_bound term.1 written; omega
      exact (RuntimeTransferRnkHash2OwnedCompletion.preserves _ term.1 not2).trans
        (RuntimeTransferRnkHash1OwnedCompletion.preserves _ term.1 not1)
    change Square (eval (completed base) row.a) (eval (completed base) row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    exact done0 row member
  have previous1 : Satisfies (completed base) RuntimeTransferRnkHash1OwnedCompletion.rawRows := by
    intro row member
    have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval (completed base) terms = eval (assignment2 base) terms := by
      apply eval_agrees
      intro term present
      have supported := support1 row member term (inside term present)
      have not2 : term.1 ∉ RuntimeTransferRnkHash2OwnedCompletion.ownedWrites := by
        intro written; have bounds := writes2_bound term.1 written; omega
      exact RuntimeTransferRnkHash2OwnedCompletion.preserves _ term.1 not2
    change Square (eval (completed base) row.a) (eval (completed base) row.b)
    rw [agrees row.a (by intro term present; exact List.mem_append_left _ present),
      agrees row.b (by intro term present; exact List.mem_append_right _ present)]
    exact done1 row member
  intro row member
  rcases List.mem_append.mp member with before | last
  · rcases List.mem_append.mp before with first | second
    · exact previous0 row first
    · exact previous1 row second
  · exact done2 row last
'''
    for export in ('preserves', 'eval_preserved', 'complete_rows'):
        source += '#print axioms '+export+'\n'
    return name, _signature_audits(source+f'end ShielddSecurity.{name}\n')
