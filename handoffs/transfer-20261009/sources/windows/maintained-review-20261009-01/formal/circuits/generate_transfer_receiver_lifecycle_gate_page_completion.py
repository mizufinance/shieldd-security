"""Compose at most eight captured lifecycle constructors with symbolic frames."""
import ast
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(page, sources):
    page = relation.natural(page, 9)
    indices = (0,1,2,*range(67,131))[page*8:(page+1)*8]
    if len(sources) != len(indices):
        raise relation.RelationError('one captured source per receiver gate required')
    gates = [f'RuntimeTransferReceiverLifecycleGate{i:03}' for i in indices]
    completions = [f'TransferReceiverLifecycleGateCompletion{i:03}' for i in indices]
    steps = []
    for gate, source in zip(gates, sources):
        if f'namespace ShielddSecurity.{gate}\n' not in source:
            raise relation.RelationError('exact captured gate namespace required')
        pivots = []
        for label in ('output','auxiliary'):
            match = re.search(r'^def '+label+r' : Linear := (\[[^\n]+\])$', source, re.M)
            if match is None:
                raise relation.RelationError('captured unit pivots required')
            terms = ast.literal_eval(re.sub(r'\((-?\d+) : Int\)', r'\1', match[1]))
            if len(terms) != 1 or terms[0][1] != 1:
                raise relation.RelationError('unit physical pivots required')
            pivots.append(terms[0][0])
        steps.append(f'CompilerCompletion.Step.product {gate}.left {gate}.right [] {pivots[0]} {pivots[1]}')
    name = f'TransferReceiverLifecycleGatePageCompletion{page:02}'
    text = 'import ShielddSecurity.CompilerSequenceCompletion\n'
    text += ''.join(f'import ShielddSecurity.{dep}\n' for dep in completions)
    text += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 200000

def indices : List Nat := {list(indices)}
def steps : List CompilerCompletion.Step := [{','.join(steps)}]
def writes : List Nat := PoseidonCompletion.writes steps
def blocks : List (List Row) := [{','.join(gate+'.rawRows' for gate in gates)}]
def rows : List Row := blocks.flatten
def completed {{F : Type}} [Field F] (base : Nat → F) : Nat → F := CompilerCompletion.run base steps

theorem preserved {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (outside : column ∉ writes) : completed base column = base column :=
  PoseidonCompletion.run_outside base steps column outside

theorem preserved_rows {{F : Type}} [Field F] (base : Nat → F) (prior : List Row)
    (satisfied : Satisfies base prior)
    (outside : ∀ row ∈ prior,∀ term ∈ row.a ++ row.b,term.1 ∉ writes) :
    Satisfies (completed base) prior :=
  CompilerSequenceCompletion.preserves_rows base steps prior satisfied outside

theorem complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base 200692 = base 0)
    (n : Nat) (flag : Bool) (flagMeaning : base 10 = if flag then 1 else 0)
    (bitMeaning : ∀ i ∈ indices,base (1849+i) = if (encodeBits 131 n)[i]?.getD false then 1 else 0)
    (legal : flag = true → ReceiverLifecycle.LegalActive n) :
    Satisfies (completed base) rows := by
  intro row member
  obtain ⟨part,present,member⟩ := List.mem_flatten.mp member
  simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with {' | '.join('rfl' for _ in indices)}
'''
    for k, (index, gate, completion) in enumerate(zip(indices, gates, completions)):
        prefix_program = '['+','.join(steps[:k])+']'
        suffix = '['+','.join(steps[k+1:])+']'
        text += f'''  · let prefixProgram : List CompilerCompletion.Step := {prefix_program}
    let suffix : List CompilerCompletion.Step := {suffix}
    let before : Nat → F := CompilerCompletion.run base prefixProgram
    have input (column : Nat) (outside : column ∉ PoseidonCompletion.writes prefixProgram) : before column = base column :=
      PoseidonCompletion.run_outside base prefixProgram column outside
    have unit : before 0 = 1 := (input 0 (by decide)).trans one
    have copy : before 200692 = before 0 := by
      rw [input 200692 (by decide),input 0 (by decide),linked]
    have flagValue : before 10 = if flag then 1 else 0 := (input 10 (by decide)).trans flagMeaning
    have bitValue : before {1849+index} = if (encodeBits 131 n)[{index}]?.getD false then 1 else 0 :=
      (input {1849+index} (by decide)).trans (bitMeaning {index} (by decide))
    have built := {completion}.complete before unit copy n flag flagValue bitValue legal
    have splitSteps : steps = prefixProgram ++ {steps[k]} :: suffix := rfl
    have assignment : completed base = CompilerCompletion.run ({completion}.completed before) suffix := by
      change CompilerCompletion.run base steps = _
      rw [splitSteps,CompilerSequenceCompletion.run_append]
      rfl
    have retained := CompilerSequenceCompletion.preserves_rows ({completion}.completed before) suffix
      {gate}.rawRows built (by decide)
    rw [assignment]
    exact retained row member
'''
    text += f'''#print axioms preserved
#print axioms preserved_rows
#print axioms complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
