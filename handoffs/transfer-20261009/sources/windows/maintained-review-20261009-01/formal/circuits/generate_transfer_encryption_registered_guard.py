"""Render independently rechecked payload identity-exclusion equations."""
from . import transfer_encryption_registered_guard as guard
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def generate(checked, extracted):
    raw, _, point, flag, c = guard.recheck(checked,extracted)
    copy = checked['metadata']['constant_copy']
    name = 'RuntimeTransferEncryptionRegisteredPayloadGuard'
    source = f'''import ShielddSecurity.RowOrientationSoundness
import ShielddSecurity.ScalarComparisonBounds
import ShielddSecurity.EncryptionRegisteredKeyGuard
namespace ShielddSecurity.{name}
set_option maxHeartbeats 250000
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {sorted(raw)}
def rawRows : List Row := [
''' + ',\n'.join('  ⟨'+linear(a)+', '+linear(b)+'⟩' for a,b in raw.values()) + f''']
def unoutlined : List Row := Compiler.unoutlineRows {copy} rawRows
def rows : List Row := unoutlined ++ unoutlined.map (fun row => ⟨scaleLinear (-1) row.a,row.b⟩)
def flag : Linear := {linear(flag)}
def point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(point[0])},eval rho {linear(point[1])}⟩
theorem link_checked : Compiler.checkRow modulus rawRows
    ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
theorem rows_checked : rows.all (fun row => Compiler.checkRow modulus unoutlined row ||
    Compiler.checkRow modulus unoutlined ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide
theorem rows_satisfied {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho rows := by
  have actual := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied link_checked
  exact RowOrientationSoundness.checked_rows rho unoutlined rows rows_checked actual
'''
    common = '''{F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows)'''
    for axis, operand in (('x',point[0]),('y',guard.combine(point[1],guard.ONE,-1))):
        cert = c[axis]
        inverse,zero,output,auxiliary = map(linear,(c['inverse_'+axis],c['zero_'+axis],cert['output'],cert['auxiliary']))
        expression = '(point rho).x' if axis == 'x' else '((point rho).y - 1)'
        source += f'''theorem {axis}_reciprocal {common} :
    {expression} * eval rho {inverse} = 1 - eval rho {zero} := by
  have actual := rows_satisfied rho satisfied
  have product := Compiler.checked_product_sound rho rows {linear(operand)} {inverse}
    {output} {auxiliary} four actual (by decide) (by decide)
  have assertion := ScalarComparisonBounds.checked_equality rho rows actual
    {output} {linear(cert['numerator'])} (by decide)
  rw [product] at assertion
  simpa [point, eval, one, sub_eq_add_neg] using assertion
'''
    source += f'''theorem forbidden_equation {common} :
    eval rho flag * eval rho {linear(c['zero_x'])} * eval rho {linear(c['zero_y'])} = 0 := by
  have actual := rows_satisfied rho satisfied
  have equal := Compiler.checked_product_sound rho rows {linear(c['zero_x'])} {linear(c['zero_y'])}
    {linear(c['equal'])} {linear(c['equal_certificate']['auxiliary'])} four actual (by decide) (by decide)
  have forbidden := Compiler.checked_product_sound rho rows flag {linear(c['equal'])}
    {linear(c['forbidden'])} {linear(c['forbidden_certificate']['auxiliary'])} four actual (by decide) (by decide)
  have assertion := ScalarComparisonBounds.checked_equality rho rows actual
    {linear(c['forbidden'])} [] (by decide)
  rw [forbidden, equal] at assertion
  simpa only [eval, mul_assoc] using assertion
theorem regulated_nonidentity {common}
    (regulated : eval rho flag = 1) : point rho ≠ Group.identityPoint := by
  exact EncryptionRegisteredKeyGuard.forbidden_identity (point rho) (eval rho flag)
    (eval rho {linear(c['zero_x'])}) (eval rho {linear(c['zero_y'])})
    (eval rho {linear(c['inverse_x'])}) (eval rho {linear(c['inverse_y'])})
    (x_reciprocal rho one four satisfied) (y_reciprocal rho one four satisfied)
    (forbidden_equation rho one four satisfied) regulated
theorem represented_nonidentity {{F J : Type}} [Field F] [CharP F modulus] [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d) (represented : J)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (meaning : model.coordinates represented = point rho)
    (satisfied : Satisfies rho rawRows) (regulated : eval rho flag = 1) : represented ≠ 0 := by
  intro zero
  have guarded := regulated_nonidentity rho one four satisfied regulated
  rw [← meaning, zero, model.identity] at guarded
  exact guarded rfl
'''
    for theorem in ('link_checked','rows_checked','rows_satisfied','x_reciprocal','y_reciprocal',
                    'forbidden_equation','regulated_nonidentity','represented_nonidentity'):
        source += '#print axioms '+theorem+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
