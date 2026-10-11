"""Include the independently supplied ProofLocation family before freezing the plan."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
source=ROOT/'handwritten/TransferCapabilityRows01.lean'
text=source.read_text()
assert '#check' not in text
(ROOT/'predecessor_no_family_source.lean.txt').write_text(text,encoding='utf-8',newline='\n')
text=text.replace('(expected : Nat → Item)', '(expected : Nat → Item) (families : Nat → Nat)')
text=text.replace('checkBindings registry expected', 'checkBindings registry expected families')
text=text.replace('check_bindings_success registry expected', 'check_bindings_success registry expected families')
text=text.replace('validate slots expected registry', 'validate slots expected families registry')
text=text.replace('validation_success slots expected registry', 'validation_success slots expected families registry')
text=text.replace('validation_bound_result slots expected registry', 'validation_bound_result slots expected families registry')
text=text.replace('validation_bound_input slots expected registry', 'validation_bound_input slots expected families registry')
text=text.replace('row.2.registry = registry ∧ row.2.item = expected row.1',
                  'row.2.registry = registry ∧ row.2.item.family = families row.1 ∧ row.2.item = expected row.1')
text=text.replace('first.2.registry = registry ∧ first.2.item = expected first.1',
                  'first.2.registry = registry ∧ first.2.item.family = families first.1 ∧ first.2.item = expected first.1')
text=text.replace('exact ⟨inserted, coverage, binding⟩', 'exact ⟨rfl, coverage, binding⟩')
old='  exact ⟨unique, sorted.trans (List.mergeSort_perm slots (fun left right => left ≤ right)),\n    check_bindings_success registry expected families result binding⟩'
new='  refine ⟨unique, sorted.trans (List.mergeSort_perm slots (fun left right => left ≤ right)), ?_⟩\n  intro row present\n  have checked := check_bindings_success registry expected families result binding row present\n  exact ⟨checked.1, checked.2.2⟩'
assert old in text
text=text.replace(old,new)
needle='theorem every_expected_slot_checked '
family='''theorem every_result_family_checked (slots : List Nat) (expected : Nat → Item)
    (families : Nat → Nat) (registry : Nat) (rows result : List (Nat × Capability))
    (success : validate slots expected families registry rows = some result) :
    ∀ row ∈ result, row.2.item.family = families row.1 := by
  have binding := (validation_success slots expected families registry rows result success).2.2
  intro row inside
  exact (check_bindings_success registry expected families result binding row inside).2.1

'''
assert text.count(needle)==1
text=text.replace(needle,family+needle)
source.write_text(text,encoding='utf-8',newline='\n')
print('Native independent location-family check added; no plan or qualified source was modified.')
