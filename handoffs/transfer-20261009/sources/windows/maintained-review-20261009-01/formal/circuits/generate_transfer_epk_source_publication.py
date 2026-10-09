"""Source-scope publication pulled back through the actual involutive captured EPK1 row map."""
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate():
    name = 'RuntimeTransferEpk0CapturedPublication'
    inverse = 'RuntimeTransferEpk1CapturedPublication.inverseRows.map (RowRenaming.row RuntimeTransferEpk1RenamingMap.columns)'
    binding = 'RuntimeTransferEpk1CapturedPublication.bindingRows.map (RowRenaming.row RuntimeTransferEpk1RenamingMap.columns)'
    text = f'''import ShielddSecurity.RuntimeTransferEpk1CapturedPublication
import ShielddSecurity.RuntimeTransferEpk1RenamingMap
import ShielddSecurity.RowOrientationSoundness
import ShielddSecurity.GroupQuotientRowSoundness
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def modulus : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513
def inverseRows : List Row := {inverse}
def bindingRows : List Row := {binding}
def expectedInverse : List Row := GroupRowCompletion.quotientRows [(200692,1)] [(4922,1)] [] 5435 91126 91127
def expectedBinding : List Row := [equalityRow 5433 4922,equalityRow 5434 4923,equalityRow 0 200692]
def rows : List Row := inverseRows ++ bindingRows

theorem inverse_checked : expectedInverse.all (fun row =>
    Compiler.checkRow modulus inverseRows row ||
    Compiler.checkRow modulus inverseRows ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide
theorem inverse_complete_checked : inverseRows.all (fun row =>
    Compiler.checkRow modulus expectedInverse row ||
    Compiler.checkRow modulus expectedInverse ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide
theorem binding_checked : expectedBinding.all (fun row =>
    Compiler.checkRow modulus bindingRows row ||
    Compiler.checkRow modulus bindingRows ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

theorem binding_complete_checked : bindingRows.all (fun row =>
    Compiler.checkRow modulus expectedBinding row ||
    Compiler.checkRow modulus expectedBinding ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

variable {{F : Type}} [Field F] [CharP F modulus]

theorem publication_sound (rho : Nat → F) (satisfied : Satisfies rho rows) :
    rho 5433 = rho 4922 ∧ rho 5434 = rho 4923 ∧ rho 0 = rho 200692 := by
  have actual : Satisfies rho bindingRows := by
    intro row member;exact satisfied row (List.mem_append_right _ member)
  have expected : Satisfies rho expectedBinding :=
    RowOrientationSoundness.checked_rows rho bindingRows expectedBinding binding_checked actual
  exact ⟨equality_row_sound expectedBinding 5433 4922 rho (by decide) expected,
    equality_row_sound expectedBinding 5434 4923 rho (by decide) expected,
    equality_row_sound expectedBinding 0 200692 rho (by decide) expected⟩

theorem inverse_sound (rho : Nat → F) (four : (4 : F) ≠ 0)
    (one : rho 0 = 1) (satisfied : Satisfies rho rows) :
    rho 5435 * rho 4922 = 1 ∧ rho 4922 ≠ 0 := by
  have actual : Satisfies rho inverseRows := by
    intro row member;exact satisfied row (List.mem_append_left _ member)
  have expected : Satisfies rho expectedInverse :=
    RowOrientationSoundness.checked_rows rho inverseRows expectedInverse inverse_checked actual
  have equation := GroupQuotientRowSoundness.product_equation rho [(200692,1)] [(4922,1)] [] 5435 91126 91127 four expected
  have linked := (publication_sound rho satisfied).2.2
  have product : rho 5435 * rho 4922 = 1 := by
    simpa only [eval,Int.cast_one,one_mul,add_zero,← linked,one] using equation
  refine ⟨product,?_⟩
  intro zero
  have impossible : (0 : F) = 1 := by simpa only [zero,mul_zero] using product
  exact zero_ne_one impossible

def publicationAssignment (rho : Nat → F) (column : Nat) : F :=
  if column = 4922 then rho 5433 else if column = 4923 then rho 5434 else rho column

def construct (rho : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient (publicationAssignment rho) [(200692,1)] [(4922,1)] [] 5435 91126 91127

def writes : List Nat := [4922,4923,5435,91126,91127]

theorem preserves (rho : Nat → F) (column : Nat) (outside : column ∉ writes) :
    construct rho column = rho column := by
  have untouched : column ≠ 4922 ∧ column ≠ 4923 ∧ column ≠ 5435 ∧
      column ≠ 91126 ∧ column ≠ 91127 := by
    simpa only [writes,List.mem_cons,List.not_mem_nil,or_false,not_or] using outside
  have small : column ∉ GroupRowCompletion.writes 5435 91126 91127 := by
    simpa only [GroupRowCompletion.writes,List.mem_cons,List.not_mem_nil,or_false,not_or] using untouched.2.2
  rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ column small]
  simp only [publicationAssignment,if_neg untouched.1,if_neg untouched.2.1]

theorem complete (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (legal : rho 5433 ≠ 0) : Satisfies (construct rho) rows := by
  have fresh : ∀ term ∈ ([(200692,1)] : Linear) ++ [(4922,1)] ++ [],
      term.1 ∉ GroupRowCompletion.writes 5435 91126 91127 := by decide
  have expected : Satisfies (construct rho) expectedInverse :=
    GroupRowCompletion.extend_complete (publicationAssignment rho) [(200692,1)] [(4922,1)] [] 5435 91126 91127
      (by decide) (by decide) (by decide) fresh (by simpa [eval,publicationAssignment] using legal)
  have actual : Satisfies (construct rho) inverseRows :=
    RowOrientationSoundness.checked_rows (construct rho) expectedInverse inverseRows inverse_complete_checked expected
  have x : construct rho 4922 = rho 5433 := by
    rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ 4922 (by decide)]
    simp [publicationAssignment]
  have y : construct rho 4923 = rho 5434 := by
    rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ 4923 (by decide)]
    simp [publicationAssignment]
  have outputX := preserves rho 5433 (by decide)
  have outputY := preserves rho 5434 (by decide)
  have unit := preserves rho 0 (by decide)
  have copy := preserves rho 200692 (by decide)
  have expectedBindingDone : Satisfies (construct rho) expectedBinding := by
    intro row member
    simp only [expectedBinding,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals simp [equalityRow,Square,eval,x,y,outputX,outputY,unit,copy,linked]
  have actualBinding : Satisfies (construct rho) bindingRows :=
    RowOrientationSoundness.checked_rows (construct rho) expectedBinding bindingRows
      binding_complete_checked expectedBindingDone
  intro row member
  rcases List.mem_append.mp member with inverseMember | bindingMember
  · exact actual row inverseMember
  · exact actualBinding row bindingMember

#print axioms inverse_checked
#print axioms inverse_complete_checked
#print axioms binding_checked
#print axioms binding_complete_checked
#print axioms publication_sound
#print axioms inverse_sound
#print axioms preserves
#print axioms complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
