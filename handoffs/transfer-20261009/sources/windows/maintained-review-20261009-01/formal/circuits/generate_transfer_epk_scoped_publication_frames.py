"""Bounded physical support certificates for the owned EPK publication writes."""
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(scope, kind, index=None):
    if type(scope) is not int or not 2 <= scope <= 5:
        raise relation.RelationError("exact genuine remaining EPK scope required")
    if kind == 'page' and type(index) is int and 0 <= index < 8:
        dependency = f'RuntimeTransferEpk{scope}TemplateRenamingPage{index:02d}'
        definition = 'targetRows'
        suffix = f'Page{index:02d}'
    elif kind == 'canonical' and type(index) is int and 0 <= index < 6:
        dependency = f'RuntimeTransferEpk{scope}RenamingRows126Part{index:03d}'
        definition = 'rawRows'
        suffix = f'CanonicalPart{index:03d}'
    elif kind == 'first' and index is None:
        dependency = f'RuntimeTransferEpk{scope}RenamingRows000'
        definition = 'rawRows'
        suffix = 'First'
    else:
        raise relation.RelationError('exact bounded EPK publication support selector required')
    name = f'RuntimeTransferEpk{scope}PublicationFrame' + suffix
    text = f'''import ShielddSecurity.{dependency}
import ShielddSecurity.RuntimeTransferEpk{scope}CapturedPublication
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

def rows : List Row := {dependency}.{definition}

theorem writes_checked : rows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ RuntimeTransferEpk{scope}CapturedPublication.writes))) = true := by decide

theorem preserves {{F : Type}} [Field F]
    [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    Satisfies (RuntimeTransferEpk{scope}CapturedPublication.construct rho) rows := by
  intro row member
  have support := List.all_eq_true.mp writes_checked row member
  have agree (terms : Linear) (included : ∀ term ∈ terms,term ∈ row.a ++ row.b) :
      eval (RuntimeTransferEpk{scope}CapturedPublication.construct rho) terms = eval rho terms := by
    apply eval_agrees
    intro term present
    exact RuntimeTransferEpk{scope}CapturedPublication.preserves rho term.1
      (of_decide_eq_true (List.all_eq_true.mp support term (included term present)))
  rw [agree row.a (by intro term present;exact List.mem_append_left _ present),
    agree row.b (by intro term present;exact List.mem_append_right _ present)]
  exact satisfied row member

#print axioms writes_checked
#print axioms preserves
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)


def generate_all(scope):
    return [generate(scope, 'first'), *[generate(scope, 'canonical', i) for i in range(6)],
            *[generate(scope, 'page', i) for i in range(8)]]
