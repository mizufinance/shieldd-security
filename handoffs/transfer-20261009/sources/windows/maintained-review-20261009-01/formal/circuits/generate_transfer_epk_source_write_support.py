"""Original captured EPK write tree and bounded own-row supports."""
from . import transfer_relation as relation
from .generate_transfer_epk_write_support import _tree_declarations
from .generate_hash_round import _signature_audits


def source_writes(pair):
    if pair.get('scope_id') != 1:
        raise relation.RelationError('genuine original-to-scope-one pair required')
    writes = pair.get('source_writes')
    if (not isinstance(writes, list) or not writes or
        any(type(c) is not int or c < 0 for c in writes) or len(writes) != len(set(writes))):
        raise relation.RelationError('actual unique original-source write list required')
    if any(c in writes for c in [0,200692,4930]) or any(c not in writes for c in [4922,4923]):
        raise relation.RelationError('original native inputs/publication writes differ')
    return sorted(writes)


def generate_tree(pair):
    writes = source_writes(pair)
    name = 'RuntimeTransferEpk0ConstructiveWriteTree'
    text = f'''import ShielddSecurity.FiniteWritePatch
namespace ShielddSecurity.{name}
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

{_tree_declarations(writes)}
def inputs : List Nat := [0,200692,4930]

theorem constant_unwritten : FiniteColumnRenaming.lookup tree 0 = none := by decide

theorem inputs_checked : inputs.all (fun column =>
    decide (FiniteColumnRenaming.lookup tree column = none)) = true := by decide

theorem publication_checked : [(4922 : Nat),4923].all
    (fun column => (FiniteColumnRenaming.lookup tree column).isSome) = true := by decide

#print axioms constant_unwritten
#print axioms inputs_checked
#print axioms publication_checked
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)


def generate_support(kind, index=None):
    if kind == 'canonical' and type(index) is int and 0 <= index < 16:
        dependency = 'RuntimeTransferEpk0Canonical';definition = f'c{index}Raw';suffix = f'CanonicalPart{index:02d}'
    elif kind == 'tail' and index is None:
        dependency = 'RuntimeTransferEpk0Canonical';definition = 'tailRaw';suffix = 'CanonicalTail'
    elif kind == 'first' and index is None:
        dependency = 'RuntimeTransferEpk0FixedWindow000';definition = 'rawRows';suffix = 'First'
    elif kind == 'page' and type(index) is int and 0 <= index < 8:
        dependency = f'RuntimeTransferEpk1TemplateRenamingPage{index:02d}';definition = 'sourceRows';suffix = f'Page{index:02d}'
    elif kind == 'publication' and index is None:
        dependency = 'RuntimeTransferEpk0CapturedPublication';definition = 'rows';suffix = 'Publication'
    else:
        raise relation.RelationError('exact bounded original-source support required')
    tree = 'RuntimeTransferEpk0ConstructiveWriteTree'
    name = 'RuntimeTransferEpk0ConstructiveOwnSupport' + suffix
    text = f'''import ShielddSecurity.{tree}
import ShielddSecurity.{dependency}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def rows : List Row := {dependency}.{definition}

theorem support_checked : rows.all (fun row => (row.a ++ row.b).all (fun term =>
    (FiniteColumnRenaming.lookup {tree}.tree term.1).isSome ||
    decide (term.1 ∈ {tree}.inputs))) = true := by decide

theorem support : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
    (FiniteColumnRenaming.lookup {tree}.tree term.1).isSome = true ∨
      term.1 ∈ {tree}.inputs := by
  intro row member term present
  have checked := List.all_eq_true.mp (List.all_eq_true.mp support_checked row member) term present
  rcases Bool.or_eq_true_iff.mp checked with selected | input
  · exact Or.inl selected
  · exact Or.inr (of_decide_eq_true input)

#print axioms support_checked
#print axioms support
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)


def generate_all_supports():
    return [*[generate_support('canonical',i) for i in range(16)],generate_support('tail'),
            generate_support('first'),*[generate_support('page',i) for i in range(8)],generate_support('publication')]
