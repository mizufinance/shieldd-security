"""Actual bounded map product/assertion join to its total rational image.

This does not establish selected-root choice, curve membership, cofactor or
native codec correspondence. Those joins use the maintained Elligator helpers.
"""
from . import transfer_asset_map as maps, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import linear, signed, _signature_audits
    result=maps.certificates(data,extracted,accepted_roles)
    checked=result['checked'];raw=result['raw'];rows=result['rows'];v=checked['values']
    inv,den,zero=v['inv'],v['den'],v['zero'];s,t,plus=v['s'],v['t'],v['plus']
    image=checked['points'][0];indices=set();products=[]

    def product(label,a,b,output=None):
        matches=[(node,out) for node,left,right,out in checked['nonlinear']
                 if ((a,b)==(left,right) or (b,a)==(left,right)) and (output is None or out==output)]
        if len(matches)!=1:raise relation.RelationError('asset rational image unique exact source product: '+label)
        node,out=matches[0];cert=arithmetic.product_certificate(a,b,out,rows)
        indices.update(cert['rows']);products.append((label,node,a,b,out,cert));return out

    product('denominator',plus,t,den)
    product('inverseProduct',den,inv,checked['products'][1])
    product('denominatorZero',den,zero,checked['products'][2])
    product('inverseZero',inv,zero,checked['products'][3])
    intermediate=product('inversePlus',inv,plus)
    product('imageX',intermediate,s,image[0])
    intermediate=product('inverseT',inv,t)
    product('imageY',intermediate,combine(s,maps.ONE,-1),combine(image[1],zero,-1))
    assertions=[]
    for label,a,b in [('productAssertion',checked['products'][1],combine(maps.ONE,zero,-1)),
                      ('denominatorAssertion',checked['products'][2],()),
                      ('inverseAssertion',checked['products'][3],())]:
        delta=combine(a,b,-1)
        if not delta:raise relation.RelationError('asset rational image nontrivial assertion required')
        direct=next((i for i,row in rows.items() if row==(delta,())),None)
        reverse=next((i for i,row in rows.items() if row==(canonical((c,-n) for c,n in delta),())),None)
        if direct is None and reverse is None:raise relation.RelationError('asset rational image original assertion missing')
        selected=direct if direct is not None else reverse;indices.add(selected)
        assertions.append((label,a,b,direct is not None))
    copy=checked['metadata']['constant_copy']
    link=next(i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),()))
    indices.add(link);name='RuntimeTransferAssetMapRationalImage'
    out=[f'''import ShielddSecurity.ScalarRows
import ShielddSecurity.Elligator
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact source metadata SHA256 {checked['metadata_sha256']}.
-- Actual local image only; root choice/curve/cofactor/native/full Transfer remain open.
def modulus : Nat := {maps.P}
def originalRows : List Nat := {sorted(indices)}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(indices))+f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
''']
    exports=['constantLink']
    for label,node,a,b,output,cert in products:
        left,right=(b,a) if cert.get('swapped') else (a,b)
        if cert['kind']=='square':datum='.square'
        elif cert['kind']=='product':datum='.product '+linear(cert['auxiliary'])
        else:datum=('.foldedLeft ' if cert['kind']=='folded_left' else '.foldedRight ')+f'({signed(cert["coefficient"])} : Int)'
        out.append(f'''-- Exact source product Node({node}); physical rows {cert['rows']}.
theorem {label} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho {linear(output)} = eval rho {linear(a)} * eval rho {linear(b)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have actual := ScalarRows.checked_product_sound rho one four rows normalized
    {linear(left)} {linear(right)} {linear(output)} ({datum}) (by decide)
  simpa only [mul_comm] using actual
''');exports.append(label)
    for label,a,b,direct in assertions:
        left,right=(a,b) if direct else (b,a)
        out.append(f'''theorem {label} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(a)} = eval rho {linear(b)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have actual := Compiler.checked_assertion_sound rho rows {linear(left)} {linear(right)} normalized (by decide)
  exact actual{'' if direct else '.symm'}
''');exports.append(label)
    out.append(f'''theorem plus_value {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    eval rho {linear(plus)} = eval rho {linear(s)} + 1 := by
  have actual := Compiler.canonical_equal rho {linear(plus)} ({linear(s)} ++ [(0,1)]) (by decide)
  simpa only [eval_append, eval, one, Int.cast_one, one_mul, add_zero] using actual

theorem minus_value {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    eval rho {linear(combine(s,maps.ONE,-1))} = eval rho {linear(s)} - 1 := by
  have actual := Compiler.canonical_equal rho {linear(combine(s,maps.ONE,-1))} (Compiler.subtract {linear(s)} [(0,1)]) (by decide)
  simpa only [Compiler.eval_subtract, eval, one, Int.cast_one, one_mul, add_zero] using actual

theorem total_inverse {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    ((eval rho {linear(s)} + 1) * eval rho {linear(t)}) * eval rho {linear(inv)} = 1 - eval rho {linear(zero)} ∧
    ((eval rho {linear(s)} + 1) * eval rho {linear(t)}) * eval rho {linear(zero)} = 0 ∧
    eval rho {linear(inv)} * eval rho {linear(zero)} = 0 := by
  have den := denominator rho one four satisfied
  rw [plus_value rho one] at den
  have p := (inverseProduct rho one four satisfied).symm.trans (productAssertion rho satisfied)
  have a := (denominatorZero rho one four satisfied).symm.trans (denominatorAssertion rho satisfied)
  have i := (inverseZero rho one four satisfied).symm.trans (inverseAssertion rho satisfied)
  rw [den] at p a
  have target := Compiler.canonical_equal rho {linear(combine(maps.ONE,zero,-1))}
    (Compiler.subtract [(0,1)] {linear(zero)}) (by decide)
  rw [target] at p
  simp only [Compiler.eval_subtract, eval, one, Int.cast_one, one_mul, add_zero] at p a i ⊢
  exact ⟨p,a,i⟩

def actualImage {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(image[0])},eval rho {linear(image[1])}⟩

theorem rational_image {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    actualImage rho = Elligator.rationalPoint (eval rho {linear(s)}) (eval rho {linear(t)}) := by
  have ix := imageX rho one four satisfied
  rw [inversePlus rho one four satisfied, plus_value rho one] at ix
  have iy := imageY rho one four satisfied
  rw [inverseT rho one four satisfied, minus_value rho one] at iy
  have difference := Compiler.canonical_equal rho {linear(combine(image[1],zero,-1))}
    (Compiler.subtract {linear(image[1])} {linear(zero)}) (by decide)
  rw [difference, Compiler.eval_subtract] at iy
  have iy' : eval rho {linear(image[1])} =
    eval rho {linear(inv)} * eval rho {linear(t)} * (eval rho {linear(s)} - 1) + eval rho {linear(zero)} :=
    sub_eq_iff_eq_add.mp iy
  have constraints := total_inverse rho one four satisfied
  have coordinates : actualImage rho =
    (⟨eval rho {linear(inv)} * (eval rho {linear(s)} + 1) * eval rho {linear(s)},
      eval rho {linear(inv)} * eval rho {linear(t)} * (eval rho {linear(s)} - 1) + eval rho {linear(zero)}⟩ : Group.Point F) := by
    unfold actualImage
    exact congrArg₂ Group.Point.mk ix iy'
  exact coordinates.trans (Elligator.rational_point_sound _ _ _ _ constraints.1 constraints.2.1 constraints.2.2)
''')
    exports.extend(['plus_value','minus_value','total_inverse','rational_image'])
    out.extend('#print axioms '+name+'\n' for name in exports)
    out.append('end ShielddSecurity.'+name+'\n')
    return name,_signature_audits(''.join(out))
