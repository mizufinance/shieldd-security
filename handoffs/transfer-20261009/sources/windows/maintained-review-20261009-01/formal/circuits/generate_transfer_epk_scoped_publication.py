"""Owned publication/inverse proofs for each genuine remaining captured EPK scope."""
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def _raw(source, scope, ordinal, indices):
    name = f'RuntimeTransferEpk{scope}RenamingRows{ordinal:03d}'
    if f'namespace ShielddSecurity.{name}\n' not in source:
        raise relation.RelationError('exact accepted publication namespace required')
    match = re.search(r'^def originalRows : List Nat := (\[.*\])$', source, re.M)
    if match is None or match[1] != str(indices):
        raise relation.RelationError('exact captured publication physical indices required')
    match = re.search(r'^def rawRows : List Row := (\[.*?\])\n(?=theorem exact_rows)', source, re.M | re.S)
    if match is None:
        raise relation.RelationError('exact accepted publication row definition required')
    return match[1]


def generate(pair, inverse_source, binding_source):
    scope = pair.get('scope_id')
    if type(scope) is not int or not 2 <= scope <= 5:
        raise relation.RelationError('exact genuine remaining captured EPK scope required')
    pairs = pair.get('restricted_map')
    if not isinstance(pairs, list) or any(not isinstance(row, list) or len(row) != 2
            or any(type(v) is not int or v < 0 for v in row) for row in pairs):
        raise relation.RelationError('typed actual scoped operand map required')
    columns = dict(pairs)
    if len(columns) != len(pairs) or len(set(columns.values())) != len(columns):
        raise relation.RelationError('injective actual scoped operand map required')
    roles = [4922,4923,5433,5434,5435,91126,91127,200692,0,4930]
    if any(role not in columns for role in roles) or columns[0] != 0 or columns[200692] != 200692:
        raise relation.RelationError('actual public/output/inverse/scalar/unit operands required')
    pub_x,pub_y,out_x,out_y,inverse_column,product,auxiliary = [columns[role] for role in roles[:7]]
    row_pairs = pair.get('original_row_map')
    if not isinstance(row_pairs,list) or any(not isinstance(row,list) or len(row)!=2
            or any(type(v)is not int or v<0 for v in row) for row in row_pairs):
        raise relation.RelationError('typed actual physical row correspondence required')
    row_map = dict(row_pairs)
    if len(row_map)!=len(row_pairs) or len(set(row_map.values()))!=len(row_map):
        raise relation.RelationError('injective actual physical row correspondence required')
    inverse = _raw(inverse_source,scope,127,[row_map[i] for i in [68388,68389,183248]])
    binding = _raw(binding_source,scope,128,[row_map[i] for i in [183246,183247,200769]])
    name = f'RuntimeTransferEpk{scope}CapturedPublication'
    text = f'''import ShielddSecurity.RowOrientationSoundness
import ShielddSecurity.GroupQuotientRowSoundness
namespace ShielddSecurity.{name}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def modulus : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513
def inverseRows : List Row := {inverse}
def bindingRows : List Row := {binding}
def expectedInverse : List Row := GroupRowCompletion.quotientRows [(200692,1)] [({pub_x},1)] [] {inverse_column} {product} {auxiliary}
def expectedBinding : List Row := [equalityRow {out_x} {pub_x},equalityRow {out_y} {pub_y},equalityRow 0 200692]
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
    rho {out_x} = rho {pub_x} ∧ rho {out_y} = rho {pub_y} ∧ rho 0 = rho 200692 := by
  have actual : Satisfies rho bindingRows := by
    intro row member;exact satisfied row (List.mem_append_right _ member)
  have expected : Satisfies rho expectedBinding :=
    RowOrientationSoundness.checked_rows rho bindingRows expectedBinding binding_checked actual
  exact ⟨equality_row_sound expectedBinding {out_x} {pub_x} rho (by decide) expected,
    equality_row_sound expectedBinding {out_y} {pub_y} rho (by decide) expected,
    equality_row_sound expectedBinding 0 200692 rho (by decide) expected⟩

theorem inverse_sound (rho : Nat → F) (four : (4 : F) ≠ 0)
    (one : rho 0 = 1) (satisfied : Satisfies rho rows) :
    rho {inverse_column} * rho {pub_x} = 1 ∧ rho {pub_x} ≠ 0 := by
  have actual : Satisfies rho inverseRows := by
    intro row member;exact satisfied row (List.mem_append_left _ member)
  have expected : Satisfies rho expectedInverse :=
    RowOrientationSoundness.checked_rows rho inverseRows expectedInverse inverse_checked actual
  have equation := GroupQuotientRowSoundness.product_equation rho [(200692,1)] [({pub_x},1)] [] {inverse_column} {product} {auxiliary} four expected
  have linked := (publication_sound rho satisfied).2.2
  have product : rho {inverse_column} * rho {pub_x} = 1 := by
    simpa only [eval,Int.cast_one,one_mul,add_zero,← linked,one] using equation
  refine ⟨product,?_⟩
  intro zero
  have impossible : (0 : F) = 1 := by simpa only [zero,mul_zero] using product
  exact zero_ne_one impossible

def publicationAssignment (rho : Nat → F) (column : Nat) : F :=
  if column = {pub_x} then rho {out_x} else if column = {pub_y} then rho {out_y} else rho column

def construct (rho : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient (publicationAssignment rho) [(200692,1)] [({pub_x},1)] [] {inverse_column} {product} {auxiliary}

def writes : List Nat := [{pub_x},{pub_y},{inverse_column},{product},{auxiliary}]

theorem preserves (rho : Nat → F) (column : Nat) (outside : column ∉ writes) :
    construct rho column = rho column := by
  have untouched : column ≠ {pub_x} ∧ column ≠ {pub_y} ∧ column ≠ {inverse_column} ∧
      column ≠ {product} ∧ column ≠ {auxiliary} := by
    simpa only [writes,List.mem_cons,List.not_mem_nil,or_false,not_or] using outside
  have small : column ∉ GroupRowCompletion.writes {inverse_column} {product} {auxiliary} := by
    simpa only [GroupRowCompletion.writes,List.mem_cons,List.not_mem_nil,or_false,not_or] using untouched.2.2
  rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ column small]
  simp only [publicationAssignment,if_neg untouched.1,if_neg untouched.2.1]

theorem complete (rho : Nat → F) (one : rho 0 = 1) (linked : rho 200692 = rho 0)
    (legal : rho {out_x} ≠ 0) : Satisfies (construct rho) rows := by
  have fresh : ∀ term ∈ ([(200692,1)] : Linear) ++ [({pub_x},1)] ++ [],
      term.1 ∉ GroupRowCompletion.writes {inverse_column} {product} {auxiliary} := by decide
  have expected : Satisfies (construct rho) expectedInverse :=
    GroupRowCompletion.extend_complete (publicationAssignment rho) [(200692,1)] [({pub_x},1)] [] {inverse_column} {product} {auxiliary}
      (by decide) (by decide) (by decide) fresh (by simpa [eval,publicationAssignment] using legal)
  have actual : Satisfies (construct rho) inverseRows :=
    RowOrientationSoundness.checked_rows (construct rho) expectedInverse inverseRows inverse_complete_checked expected
  have x : construct rho {pub_x} = rho {out_x} := by
    rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ {pub_x} (by decide)]
    simp [publicationAssignment]
  have y : construct rho {pub_y} = rho {out_y} := by
    rw [construct,GroupRowCompletion.extend_preserves _ _ _ _ _ _ _ {pub_y} (by decide)]
    simp [publicationAssignment]
  have outputX := preserves rho {out_x} (by decide)
  have outputY := preserves rho {out_y} (by decide)
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
