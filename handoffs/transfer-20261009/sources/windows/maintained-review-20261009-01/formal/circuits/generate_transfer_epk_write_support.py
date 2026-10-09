"""Real captured write trees and bounded supports for EPK constructor patches."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def _balanced(columns):
    if not columns:
        return 'FiniteColumnRenaming.Tree.empty'
    if len(columns)==1:
        return f'(.leaf {columns[0]} {columns[0]})'
    middle=len(columns)//2
    return f'(.branch {columns[middle]} {_balanced(columns[:middle])} {_balanced(columns[middle:])})'


def _tree_declarations(columns, page_size=64):
    """Bound declaration elaboration; branches keep the exact sorted lookup."""
    parts = []
    lines = []
    for ordinal, start in enumerate(range(0, len(columns), page_size)):
        page = columns[start:start + page_size]
        name = f'writePart{ordinal:03d}'
        lines.append(f'def {name} : FiniteColumnRenaming.Tree := {_balanced(page)}')
        parts.append((page[0], name))

    def assemble(items):
        if not items:
            return 'FiniteColumnRenaming.Tree.empty'
        if len(items) == 1:
            return items[0][1]
        middle = len(items) // 2
        return f'(.branch {items[middle][0]} {assemble(items[:middle])} {assemble(items[middle:])})'

    lines.append(f'def tree : FiniteColumnRenaming.Tree := {assemble(parts)}')
    return '\n'.join(lines)


def _operands(pair):
    scope=pair.get('scope_id')
    if type(scope)is not int or not 1<=scope<=5:
        raise relation.RelationError('exact genuine captured target EPK scope required')
    writes=pair.get('target_writes')
    if (not isinstance(writes,list) or not writes or any(type(c)is not int or c<0 for c in writes)
            or len(writes)!=len(set(writes))):
        raise relation.RelationError('actual unique captured constructor writes required')
    columns=dict(pair['restricted_map'])
    inputs=[0,200692,columns[4930]]
    if columns.get(0)!=0 or columns.get(200692)!=200692 or any(c in writes for c in inputs):
        raise relation.RelationError('actual unit/copy/private-scalar inputs must be unwritten')
    if columns[4922] not in writes or columns[4923] not in writes:
        raise relation.RelationError('actual native publication columns must be written')
    return scope,sorted(writes),inputs,columns


def generate_tree(pair):
    scope,writes,inputs,columns=_operands(pair)
    name=f'RuntimeTransferEpk{scope}ConstructiveWriteTree'
    text=f'''import ShielddSecurity.FiniteWritePatch
namespace ShielddSecurity.{name}
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

{_tree_declarations(writes)}
def inputs : List Nat := {inputs}

theorem constant_unwritten : FiniteColumnRenaming.lookup tree 0 = none := by decide

theorem inputs_checked : inputs.all (fun column =>
    decide (FiniteColumnRenaming.lookup tree column = none)) = true := by decide

theorem publication_checked : [({columns[4922]} : Nat),{columns[4923]}].all
    (fun column => (FiniteColumnRenaming.lookup tree column).isSome) = true := by decide

#print axioms constant_unwritten
#print axioms inputs_checked
#print axioms publication_checked
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)


def generate_support(pair,kind,index=None):
    scope,_,_,_=_operands(pair)
    if kind=='first' and index is None:
        dependency=f'RuntimeTransferEpk{scope}RenamingRows000';definition='rawRows';suffix='First'
    elif kind=='canonical' and type(index)is int and 0<=index<6:
        dependency=f'RuntimeTransferEpk{scope}RenamingRows126Part{index:03d}'
        definition='rawRows';suffix=f'CanonicalPart{index:03d}'
    elif kind=='page' and type(index)is int and 0<=index<8:
        dependency=f'RuntimeTransferEpk{scope}TemplateRenamingPage{index:02d}'
        definition='targetRows';suffix=f'Page{index:02d}'
    elif kind=='publication' and index is None:
        dependency=f'RuntimeTransferEpk{scope}CapturedPublication';definition='rows';suffix='Publication'
    else:
        raise relation.RelationError('exact bounded EPK support slice required')
    tree=f'RuntimeTransferEpk{scope}ConstructiveWriteTree'
    name=f'RuntimeTransferEpk{scope}ConstructiveOwnSupport{suffix}'
    text=f'''import ShielddSecurity.{tree}
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
    return name,_signature_audits(text)
