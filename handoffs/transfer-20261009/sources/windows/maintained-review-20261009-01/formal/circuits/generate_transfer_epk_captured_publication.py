"""Owned inverse and publication proofs from the exact accepted EPK1 rows."""
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def _raw(source, ordinal, indices):
    name = f'RuntimeTransferEpk1RenamingRows{ordinal:03d}'
    if f'namespace ShielddSecurity.{name}\n' not in source:
        raise relation.RelationError('exact accepted publication namespace required')
    match = re.search(r'^def originalRows : List Nat := (\[.*\])$', source, re.M)
    if match is None or match[1] != str(indices):
        raise relation.RelationError('exact captured publication physical indices required')
    match = re.search(r'^def rawRows : List Row := (\[.*?\])\n(?=theorem exact_rows)', source, re.M | re.S)
    if match is None:
        raise relation.RelationError('exact accepted publication row definition required')
    return match[1]


def generate(inverse_source, binding_source):
    inverse = _raw(inverse_source, 127, [78715, 78716, 184651])
    binding = _raw(binding_source, 128, [184649, 184650, 200769])
    name = 'RuntimeTransferEpk1CapturedPublication'
    text = f'''import ShielddSecurity.RowOrientationSoundness
import ShielddSecurity.GroupQuotientRowSoundness
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def modulus : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513
def inverseRows : List Row := {inverse}
def bindingRows : List Row := {binding}
def expectedInverse : List Row := GroupRowCompletion.quotientRows [(200692,1)] [(6326,1)] [] 6839 101453 101454
def expectedBinding : List Row := [equalityRow 6837 6326,equalityRow 6838 6327,equalityRow 0 200692]
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

variable {{F : Type}} [Field F] [CharP F modulus]

theorem publication_sound (rho : Nat → F) (satisfied : Satisfies rho rows) :
    rho 6837 = rho 6326 ∧ rho 6838 = rho 6327 ∧ rho 0 = rho 200692 := by
  have actual : Satisfies rho bindingRows := by
    intro row member;exact satisfied row (List.mem_append_right _ member)
  have expected : Satisfies rho expectedBinding :=
    RowOrientationSoundness.checked_rows rho bindingRows expectedBinding binding_checked actual
  exact ⟨equality_row_sound expectedBinding 6837 6326 rho (by decide) expected,
    equality_row_sound expectedBinding 6838 6327 rho (by decide) expected,
    equality_row_sound expectedBinding 0 200692 rho (by decide) expected⟩

theorem inverse_sound (rho : Nat → F) (four : (4 : F) ≠ 0)
    (one : rho 0 = 1) (satisfied : Satisfies rho rows) :
    rho 6839 * rho 6326 = 1 ∧ rho 6326 ≠ 0 := by
  have actual : Satisfies rho inverseRows := by
    intro row member;exact satisfied row (List.mem_append_left _ member)
  have expected : Satisfies rho expectedInverse :=
    RowOrientationSoundness.checked_rows rho inverseRows expectedInverse inverse_checked actual
  have equation := GroupQuotientRowSoundness.product_equation rho [(200692,1)] [(6326,1)] [] 6839 101453 101454 four expected
  have linked := (publication_sound rho satisfied).2.2
  have product : rho 6839 * rho 6326 = 1 := by
    simpa only [eval,Int.cast_one,one_mul,add_zero,← linked,one] using equation
  refine ⟨product,?_⟩
  intro zero
  have impossible : (0 : F) = 1 := by simpa only [zero,mul_zero] using product
  exact zero_ne_one impossible

def publicationAssignment (rho : Nat → F) (column : Nat) : F :=
  if column = 6326 then rho 6837 else if column = 6327 then rho 6838 else rho column

def construct (rho : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient (publicationAssignment rho) [(200692,1)] [(6326,1)] [] 6839 101453 101454

def writes : List Nat := [6326,6327,6839,101453,101454]

theorem preserves (rho : Nat → F) (column : Nat) (outside : column ∉ writes) :
    construct rho column = rho column := by
  have untouched : column ≠ 6326 ∧ column ≠ 6327 ∧ column ≠ 6839 ∧
      column ≠ 101453 ∧ column ≠ 101454 := by
    simpa only [writes,List.mem_cons,List.not_mem_nil,or_false,not_or] using outside
  have small : column ∉ GroupRowCompletion.writes 6839 101453 101454 := by
    simpa only [GroupRowCompletion.writes,List.mem_cons,List.not_mem_nil,or_false,not_or] using untouched.2.2
  rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ column small]
  simp only [publicationAssignment,if_neg untouched.1,if_neg untouched.2.1]

theorem complete (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (legal : rho 6837 ≠ 0) : Satisfies (construct rho) rows := by
  have fresh : ∀ term ∈ ([(200692,1)] : Linear) ++ [(6326,1)] ++ [],
      term.1 ∉ GroupRowCompletion.writes 6839 101453 101454 := by decide
  have expected : Satisfies (construct rho) expectedInverse :=
    GroupRowCompletion.extend_complete (publicationAssignment rho) [(200692,1)] [(6326,1)] [] 6839 101453 101454
      (by decide) (by decide) (by decide) fresh (by simpa [eval,publicationAssignment] using legal)
  have actual : Satisfies (construct rho) inverseRows :=
    RowOrientationSoundness.checked_rows (construct rho) expectedInverse inverseRows inverse_complete_checked expected
  have x : construct rho 6326 = rho 6837 := by
    rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ 6326 (by decide)]
    simp [publicationAssignment]
  have y : construct rho 6327 = rho 6838 := by
    rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ 6327 (by decide)]
    simp [publicationAssignment]
  have outputX := preserves rho 6837 (by decide)
  have outputY := preserves rho 6838 (by decide)
  have unit := preserves rho 0 (by decide)
  have copy := preserves rho 200692 (by decide)
  intro row member
  rcases List.mem_append.mp member with inverseMember | bindingMember
  · exact actual row inverseMember
  · simp only [bindingRows,List.mem_cons,List.not_mem_nil,or_false] at bindingMember
    rcases bindingMember with rfl | rfl | rfl
    all_goals simp [Square,eval,x,y,outputX,outputY,unit,copy,linked]

#print axioms inverse_checked
#print axioms inverse_complete_checked
#print axioms binding_checked
#print axioms publication_sound
#print axioms inverse_sound
#print axioms preserves
#print axioms complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
