"""Bounded original-source row frames for the captured EPK publication patch."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(kind, index=None):
    if kind == 'canonical' and type(index) is int and 0 <= index < 16:
        dependency = 'RuntimeTransferEpk0Canonical'
        definition = f'c{index}Raw'
        suffix = f'CanonicalPart{index:02d}'
    elif kind == 'tail' and index is None:
        dependency = 'RuntimeTransferEpk0Canonical'
        definition = 'tailRaw'
        suffix = 'CanonicalTail'
    elif kind == 'first' and index is None:
        dependency = 'RuntimeTransferEpk0FixedWindow000'
        definition = 'rawRows'
        suffix = 'First'
    elif kind == 'page' and type(index) is int and 0 <= index < 8:
        dependency = f'RuntimeTransferEpk1TemplateRenamingPage{index:02d}'
        definition = 'sourceRows'
        suffix = f'Page{index:02d}'
    else:
        raise relation.RelationError('exact bounded original-source publication frame required')
    name = 'RuntimeTransferEpk0PublicationFrame' + suffix
    publication = 'RuntimeTransferEpk0CapturedPublication'
    text = f'''import ShielddSecurity.{dependency}
import ShielddSecurity.{publication}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def rows : List Row := {dependency}.{definition}

theorem writes_checked : rows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ {publication}.writes))) = true := by decide

theorem preserves {{F : Type}} [Field F]
    [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    Satisfies ({publication}.construct rho) rows := by
  intro row member
  have support := List.all_eq_true.mp writes_checked row member
  have agree (terms : Linear) (included : ∀ term ∈ terms,term ∈ row.a ++ row.b) :
      eval ({publication}.construct rho) terms = eval rho terms := by
    apply eval_agrees
    intro term present
    exact {publication}.preserves rho term.1
      (of_decide_eq_true (List.all_eq_true.mp support term (included term present)))
  rw [agree row.a (by intro term present;exact List.mem_append_left _ present),
    agree row.b (by intro term present;exact List.mem_append_right _ present)]
  exact satisfied row member

#print axioms writes_checked
#print axioms preserves
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)


def generate_all():
    return [*[generate('canonical', i) for i in range(16)], generate('tail'),
            generate('first'), *[generate('page', i) for i in range(8)]]
