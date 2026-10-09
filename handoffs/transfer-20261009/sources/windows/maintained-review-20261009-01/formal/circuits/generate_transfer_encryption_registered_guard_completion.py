"""Render a finite actual-row constructor with explicit sixteen-column writes."""
from . import transfer_encryption_registered_guard_completion as completion
from . import transfer_relation as relation
from .generate_hash_round import linear,_signature_audits


def generate(checked,extracted):
    raw,_,point,flag,c,writes = completion.recheck(checked,extracted)
    x,y,regulated = [lc[0][0] for lc in (*point,flag)]
    copy = checked['metadata']['constant_copy']
    name = 'RuntimeTransferEncryptionRegisteredPayloadCompletion'
    meaning = 'RuntimeTransferEncryptionRegisteredPayloadGuard'
    fresh = list(writes.values())
    source = f'''import ShielddSecurity.{meaning}
import ShielddSecurity.EncryptionRegisteredKeyCompletion
namespace ShielddSecurity.{name}
set_option maxHeartbeats 350000
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {sorted(raw)}
def rawRows : List Row := [
''' + ',\n'.join('  ⟨'+linear(a)+', '+linear(b)+'⟩' for a,b in raw.values()) + f''']
def fresh : List Nat := {fresh}
def point {{F : Type}} [Field F] (base : Nat → F) : Group.Point F := ⟨base {x},base {y}⟩
def witness {{F : Type}} [Field F] [DecidableEq F] (base : Nat → F) :=
  EncryptionRegisteredKeyCompletion.construct (point base) (base {regulated})
'''
    expr = {}
    for axis,value in (('x',f'base {x}'),('y',f'(base {y} - 1)')):
        zero = 'zeroX' if axis == 'x' else 'zeroY'
        inverse = 'inverseX' if axis == 'x' else 'inverseY'
        expr.update({
            'zero_'+axis:f'(witness base).{zero}',
            'inverse_'+axis:f'(witness base).{inverse}',
            'reciprocal_output_'+axis:f'{value} * (witness base).{inverse}',
            'reciprocal_auxiliary_'+axis:f'({value} - (witness base).{inverse}) ^ 2',
            'annihilator_output_'+axis:f'{value} * (witness base).{zero}',
            'annihilator_auxiliary_'+axis:f'({value} - (witness base).{zero}) ^ 2',
        })
    expr.update(equal='(witness base).equal',
        equal_auxiliary='((witness base).zeroX - (witness base).zeroY) ^ 2',
        forbidden='(witness base).forbidden',
        forbidden_auxiliary=f'(base {regulated} - (witness base).equal) ^ 2')
    source += '''def values {F : Type} [Field F] [DecidableEq F]
    (base : Nat → F) (column : Nat) : F :=
'''
    for key,column in writes.items():
        source += f'  if column = {column} then {expr[key]} else\n'
    source += '''  base column
def extend {F : Type} [Field F] [DecidableEq F] (base : Nat → F) : Nat → F :=
  patchAssignment base (values base) fresh
'''
    source += f'''theorem write_shape_checked : fresh.Nodup ∧
    ∀ column ∈ {[0,copy,x,y,regulated]}, column ∉ fresh := by decide
theorem point_role {{F : Type}} [Field F] (base : Nat → F) :
    point base = {meaning}.point base := by
  simp only [point, {meaning}.point, eval, Int.cast_one, one_mul, add_zero]
theorem preserves {{F : Type}} [Field F] [DecidableEq F] (base : Nat → F)
    (column : Nat) (outside : column ∉ fresh) : extend base column = base column :=
  patchAssignment_preserves base (values base) fresh column outside
'''
    for key,column in writes.items():
        source += f'''private theorem value_{key} {{F : Type}} [Field F] [DecidableEq F]
    (base : Nat → F) : extend base {column} = {expr[key]} := by
  simp only [extend, patchAssignment, fresh, values]
  norm_num
'''
    common = f'''{{F : Type}} [Field F] [DecidableEq F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base {copy} = 1)
    (boolean : base {regulated} = 0 ∨ base {regulated} = 1)
    (legal : base {regulated} = 1 → point base ≠ Group.identityPoint)'''
    source += f'''theorem constructs {common} : Satisfies (extend base) rawRows := by
  have equations := EncryptionRegisteredKeyCompletion.construct_equations
    (point base) (base {regulated}) boolean legal
  change EncryptionRegisteredKeyCompletion.Equations (point base) (base {regulated}) (witness base) at equations
  have rx := equations.reciprocalX
  have ry := equations.reciprocalY
  have ax := equations.annihilatorX
  have ay := equations.annihilatorY
  change base {x} * (witness base).inverseX = 1 - (witness base).zeroX at rx
  change (base {y} - 1) * (witness base).inverseY = 1 - (witness base).zeroY at ry
  change base {x} * (witness base).zeroX = 0 at ax
  change (base {y} - 1) * (witness base).zeroY = 0 at ay
  have bx : (witness base).zeroX * (witness base).zeroX = (witness base).zeroX := by
    rcases equations.booleanX with zeroValue | oneValue
    · simp only [zeroValue, zero_mul]
    · simp only [oneValue, one_mul]
  have by_ : (witness base).zeroY * (witness base).zeroY = (witness base).zeroY := by
    rcases equations.booleanY with zeroValue | oneValue
    · simp only [zeroValue, zero_mul]
    · simp only [oneValue, one_mul]
'''
    for label,column in (('zero',0),('copy',copy),('x',x),('y',y),('regulated',regulated)):
        source += f'  have at_{label} := preserves base {column} (by decide : {column} ∉ fresh)\n'
    source += '''  intro row member
  simp only [rawRows, List.mem_cons, List.mem_singleton] at member
  rcases member with ''' + ' | '.join(['rfl']*len(raw)) + '\n'
    simp = ['Square','eval','Int.cast_neg','Int.cast_ofNat','Int.cast_one','Int.cast_zero',
            'one_mul','zero_mul','add_zero',
            *['value_'+key for key in writes],
            *['at_'+key for key in ('zero','copy','x','y','regulated')],'one','linked']
    source += '  all_goals simp only ['+', '.join(simp)+']\n'
    source += '''  all_goals first
    | ring
    | (simp only [bx, by_, rx, ry, ax, ay, equations.equalProduct, equations.forbiddenProduct] <;> ring)
    | (simp only [equations.forbiddenZero] <;> ring)
'''
    source += '''theorem preserves_prior {F : Type} [Field F] [DecidableEq F]
    (base : Nat → F) (prior : List Row) (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ fresh) :
    Satisfies (extend base) prior :=
  patch_preserves_rows base (values base) fresh prior satisfied disjoint
'''
    source += f'''theorem constructs_and_preserves {common} :
    Satisfies (extend base) rawRows ∧ ∀ column ∉ fresh, extend base column = base column := by
  exact ⟨constructs base one linked boolean legal, preserves base⟩
'''
    for theorem in ('write_shape_checked','point_role','preserves','constructs','preserves_prior','constructs_and_preserves'):
        source += '#print axioms '+theorem+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
