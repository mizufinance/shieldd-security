"""Bounded actual source/row recipe for first cubic and native QR choice.

Exact generated product/inverse dependencies retain their original row sets.
Global field cardinality and the pinned sqrt-option specification are explicit.
No selected native Boolean, cubic equation or output equality is assumed.
"""
from . import transfer_asset_map as maps, transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def generate(data, extracted, accepted_roles):
    from .generate_hash_round import linear, _signature_audits
    result=maps.certificates(data,extracted,accepted_roles);checked=result['checked']
    v=checked['values'];nodes=checked['nonlinear'];raw=result['raw'];rows=result['rows']
    selected_nodes={}
    def product(label,a,b,output=None):
        matches=[(offset,node,out) for offset,(node,left,right,out) in enumerate(nodes)
                 if ((a,b)==(left,right) or (b,a)==(left,right)) and (output is None or out==output)]
        if len(matches)!=1:raise relation.RelationError('map choice exact unique source product '+label)
        offset,node,out=matches[0];selected_nodes[label]=(offset//16,node);return out
    cubic=product('cubicFirst',combine(v['x1'],maps._constant(maps.C1)),v['x1'])
    product('cubicSecond',combine(cubic,maps._constant(maps.C2)),v['x1'],v['gx1'])
    product('qrSquare',v['qr_root'],v['qr_root'],checked['qr'][0])
    delta=combine(v['gx1'],maps._scale(v['gx1'],5),-1)
    selector=product('qrSelector',v['square'],delta,combine(checked['qr'][1],maps._scale(v['gx1'],5),-1))
    product('alternative',v['tv'],v['gx1'],v['gx2'])
    x_delta=combine(v['x1'],v['x2'],-1);y_delta=combine(v['gx1'],v['gx2'],-1)
    x_selector=product('selectedX',v['square'],x_delta,combine(v['x'],v['x2'],-1))
    y_selector=product('selectedY',v['square'],y_delta,combine(v['y_squared'],v['gx2'],-1))
    product('selectedSquare',v['y'],v['y'],checked['products'][0])
    chunks=sorted({chunk for chunk,_ in selected_nodes.values()})
    copy=checked['metadata']['constant_copy'];indices=set()
    link=next(i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),()))
    indices.add(link)
    boolean=next(i for i,row in rows.items() if row==(v['square'],v['square']))
    indices.add(boolean)
    a,b=checked['qr'];diff=combine(a,b,-1)
    forward=True
    if diff:
        match=next((i for i,row in rows.items() if row==(diff,())),None)
        if match is None:
            match=next((i for i,row in rows.items() if row==(canonical((c,-n) for c,n in diff),())),None)
            forward=False
        if match is None:raise relation.RelationError('map choice original QR assertion missing')
        indices.add(match)
    root_left,root_right=checked['products'][0],v['y_squared'];root_delta=combine(root_left,root_right,-1);root_forward=True
    if root_delta:
        match=next((i for i,row in rows.items() if row==(root_delta,())),None)
        if match is None:
            match=next((i for i,row in rows.items() if row==(canonical((c,-n) for c,n in root_delta),())),None);root_forward=False
        if match is None:raise relation.RelationError('map choice original selected-square assertion missing')
        indices.add(match)
    imports=['RuntimeTransferAssetMapProducts'+str(i) for i in chunks]+['RuntimeTransferAssetMapInverses']
    name='RuntimeTransferAssetMapChoice'
    source=''.join('import ShielddSecurity.'+n+'\n' for n in imports)
    source+='''import ShielddSecurity.RuntimeElligatorAlgebra
import ShielddSecurity.ElligatorNative
import ShielddSecurity.ScalarBits
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
namespace ShielddSecurity.RuntimeTransferAssetMapChoice
'''
    source+=f'''-- Exact source metadata SHA256 {checked['metadata_sha256']}.
def modulus : Nat := {maps.P}
def assertionOriginalRows : List Nat := {sorted(indices)}
def assertionRawRows : List Row := [
'''+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(indices))+f''']
def assertionRows : List Row := Compiler.unoutlineRows {copy} assertionRawRows
def rawRows : List Row := '''+' ++ '.join(n+'.rawRows' for n in imports)+' ++ assertionRawRows\n'
    for label,lc in [('tv',v['tv']),('den',v['den1']),('inverse',v['inv1']),('x1',v['x1']),
                     ('gx1',v['gx1']),('qrRoot',v['qr_root']),('square',v['square']),
                     ('x2',v['x2']),('gx2',v['gx2']),('x',v['x']),('ySquared',v['y_squared']),('y',v['y']),
                     ('s',v['s']),('t',v['t'])]:
        source+='def '+label+' : Linear := '+linear(lc)+'\n'
    source+='''noncomputable def choice {F : Type} [Field F] (rho : Nat → F) : Bool :=
  ScalarBits.decodeBit rho square
'''
    exports=['constantLink']
    source+=f'''theorem constantLink : Compiler.checkRow modulus assertionRawRows
    ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
'''
    for dependency in imports+['assertion']:
        symbol=dependency+'.rawRows' if dependency!='assertion' else 'assertionRawRows'
        suffix='included_'+dependency
        source+=f'''theorem {suffix} : ∀ row ∈ {symbol}, row ∈ rawRows := by
  intro row member
  simp only [rawRows,List.mem_append]
  tauto
''';exports.append(suffix)
    def premise(dependency):
        return f'(fun row member => satisfied row (included_{dependency} row member))'
    def node(label):
        chunk,index=selected_nodes[label];dependency='RuntimeTransferAssetMapProducts'+str(chunk)
        return f'{dependency}.node{index}_sound rho one four '+premise(dependency)
    source+=f'''theorem first_coordinate {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    (1 + eval rho tv) * eval rho x1 = -(RuntimeElligatorAlgebra.c1 : F) := by
  have reciprocal := RuntimeTransferAssetMapInverses.equation0_sound rho one four {premise('RuntimeTransferAssetMapInverses')}
  change eval rho inverse * eval rho den = eval rho [(0,1)] at reciprocal
  have unit : eval rho [(0,1)] = (1 : F) := by simp [eval,one]
  rw [unit] at reciprocal
  have denominator := Compiler.canonical_equal rho den ([(0,1)] ++ tv) (by decide)
  rw [eval_append,unit] at denominator
  have coordinate := Compiler.canonical_equal rho x1
    (scaleLinear (-RuntimeElligatorAlgebra.c1) inverse) (by decide)
  rw [eval_scale,Int.cast_neg] at coordinate
  rw [coordinate]
  calc
    _ = -(RuntimeElligatorAlgebra.c1 : F) * (eval rho inverse * eval rho den) := by rw [denominator]; ring
    _ = _ := by rw [reciprocal]; ring

theorem actual_cubic {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho gx1 = Elligator.cubic (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (eval rho x1) := by
  have first := {node('cubicFirst')}
  have second := {node('cubicSecond')}
  have firstAdd := Compiler.canonical_equal rho {linear(combine(v['x1'],maps._constant(maps.C1)))}
    (x1 ++ [(0,RuntimeElligatorAlgebra.c1)]) (by decide)
  have secondAdd := Compiler.canonical_equal rho {linear(combine(cubic,maps._constant(maps.C2)))}
    ({linear(cubic)} ++ [(0,RuntimeElligatorAlgebra.c2)]) (by decide)
  have c1Value : eval rho [(0,RuntimeElligatorAlgebra.c1)] = (RuntimeElligatorAlgebra.c1 : F) := by simp [eval,one]
  have c2Value : eval rho [(0,RuntimeElligatorAlgebra.c2)] = (RuntimeElligatorAlgebra.c2 : F) := by simp [eval,one]
  rw [eval_append,c1Value] at firstAdd
  rw [eval_append,c2Value] at secondAdd
  rw [firstAdd] at first
  rw [secondAdd,first] at second
  exact second

theorem qr_equation {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho qrRoot * eval rho qrRoot =
      if choice rho then eval rho gx1 else 5 * eval rho gx1 := by
  classical
  have normalized := Compiler.unoutline_rows_sound rho {copy} assertionRawRows
    {premise('assertion')} constantLink
  have bit : eval rho square = if choice rho then 1 else 0 :=
    ScalarBits.decoded_bit_value rho square
      (Compiler.checked_row_sound rho assertionRows ⟨square,square⟩ normalized (by decide))
  change eval rho {linear(v['square'])} = if choice rho then 1 else 0 at bit
  have squared := {node('qrSquare')}
  have selector := {node('qrSelector')}
  have target : eval rho {linear(a)} = eval rho {linear(b)} := by
'''
    if not diff:source+='    exact Compiler.canonical_equal rho _ _ (by decide)\n'
    else:
        left,right=(a,b) if forward else (b,a)
        proof=f'Compiler.checked_assertion_sound rho assertionRows {linear(left)} {linear(right)} normalized (by decide)'
        source+='    exact '+(proof if forward else '('+proof+').symm')+'\n'
    source+=f'''  have selected := Compiler.canonical_equal rho {linear(b)}
    (scaleLinear 5 gx1 ++ {linear(selector)}) (by decide)
  have difference := Compiler.canonical_equal rho {linear(delta)}
    (Compiler.subtract gx1 (scaleLinear 5 gx1)) (by decide)
  rw [eval_append,eval_scale] at selected
  rw [Compiler.eval_subtract,eval_scale] at difference
  norm_num only at selected difference
  change eval rho {linear(b)} = 5 * eval rho gx1 + eval rho {linear(selector)} at selected
  change eval rho {linear(delta)} = eval rho gx1 - 5 * eval rho gx1 at difference
  have equation := squared.symm.trans target
  rw [selected,selector,difference,bit] at equation
  calc
    _ = _ := equation
    _ = _ := by cases choice rho <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

theorem cubic_nonzero {{F : Type}} [Field F] [CharP F modulus] [Fintype F]
    (cardinality : Fintype.card F = modulus) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho gx1 ≠ 0 := by
  rw [actual_cubic rho one four satisfied]
  exact RuntimeElligatorAlgebra.first_cubic_nonzero cardinality _ _ (first_coordinate rho one four satisfied)

theorem native_choice {{F : Type}} [Field F] [CharP F modulus] [Fintype F]
    (cardinality : Fintype.card F = modulus) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows)
    (nativeOption : Bool) (sqrtSpecification : nativeOption = true ↔ ∃ root : F, root * root = eval rho gx1) :
    choice rho = nativeOption := by
  have nonzero : (5 : F) ≠ 0 := by
    intro zero
    have impossible : (5 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
  exact ElligatorNative.choice_unique 5 (eval rho gx1) (eval rho qrRoot) (choice rho) nativeOption
    (by simpa only [RuntimeElligatorParameters.z,Int.cast_ofNat] using RuntimeElligatorParameters.z_nonsquare (F := F) cardinality)
    nonzero (cubic_nonzero cardinality rho one four satisfied)
    (qr_equation rho one four satisfied) sqrtSpecification
'''
    source+=f"""theorem choice_value {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho square = if choice rho then 1 else 0 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} assertionRawRows
    {premise('assertion')} constantLink
  exact ScalarBits.decoded_bit_value rho square
    (Compiler.checked_row_sound rho assertionRows ⟨square,square⟩ normalized (by decide))
"""
    for label,yes,no,value,output,difference in [('selected_x',v['x1'],v['x2'],v['x'],x_selector,x_delta),
                                                ('selected_y_squared',v['gx1'],v['gx2'],v['y_squared'],y_selector,y_delta)]:
        product_label='selectedX' if label=='selected_x' else 'selectedY'
        source+=f"""theorem {label} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho {linear(value)} = if choice rho then eval rho {linear(yes)} else eval rho {linear(no)} := by
  have selected := Compiler.checked_add_sound rho {linear(no)} {linear(output)} {linear(value)} (by decide)
  have multiplied := {node(product_label)}
  have difference := Compiler.canonical_equal rho {linear(difference)}
    (Compiler.subtract {linear(yes)} {linear(no)}) (by decide)
  rw [Compiler.eval_subtract] at difference
  have bit := choice_value rho satisfied
  change eval rho {linear(v['square'])} = if choice rho then 1 else 0 at bit
  rw [selected,multiplied,difference,bit]
  cases choice rho <;> simp <;> ring
"""
    source+=f"""theorem selected_square {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho y * eval rho y = if choice rho then eval rho gx1 else eval rho gx2 := by
  have squared := {node('selectedSquare')}
  have equal : eval rho {linear(root_left)} = eval rho {linear(root_right)} := by
"""
    if not root_delta:source+='    exact Compiler.canonical_equal rho _ _ (by decide)\n'
    else:
        l,r=(root_left,root_right) if root_forward else (root_right,root_left)
        proof=f'Compiler.checked_assertion_sound rho assertionRows {linear(l)} {linear(r)} normalized (by decide)'
        source+=f"""    have normalized := Compiler.unoutline_rows_sound rho {copy} assertionRawRows
      {premise('assertion')} constantLink
    exact """+(proof if root_forward else '('+proof+').symm')+'\n'
    source+=f"""  exact squared.symm.trans (equal.trans (selected_y_squared rho one four satisfied))

+theorem selected_root {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho y * eval rho y = Elligator.cubic (RuntimeElligatorAlgebra.c1 : F)
      (RuntimeElligatorAlgebra.c2 : F) (eval rho x) := by
  have point := selected_x rho one four satisfied
  have root := selected_square rho one four satisfied
  have alternative := {node('alternative')}
  change eval rho x = if choice rho then eval rho x1 else eval rho x2 at point
  change eval rho gx2 = eval rho tv * eval rho gx1 at alternative
  have secondX := Compiler.canonical_equal rho x2
    (Compiler.subtract (scaleLinear (-1) x1) [(0,RuntimeElligatorAlgebra.c1)]) (by decide)
  have constant : eval rho [(0,RuntimeElligatorAlgebra.c1)] = (RuntimeElligatorAlgebra.c1 : F) := by simp [eval,one]
  rw [Compiler.eval_subtract,eval_scale,constant] at secondX
  have secondX' : eval rho x2 = -eval rho x1 - (RuntimeElligatorAlgebra.c1 : F) := by simpa using secondX
  have cubic := Elligator.alternative_cubic (RuntimeElligatorAlgebra.c1 : F)
    (RuntimeElligatorAlgebra.c2 : F) (eval rho x1) (eval rho tv) (first_coordinate rho one four satisfied)
  rw [← secondX',← actual_cubic rho one four satisfied] at cubic
  cases eqChoice : choice rho
  · simp only [eqChoice,Bool.false_eq_true,if_false] at point root
    rw [point]
    exact root.trans (alternative.trans cubic.symm)
  · simp only [eqChoice,if_true] at point root
    rw [point]
    exact root.trans (actual_cubic rho one four satisfied)
""".replace('\n+theorem','\ntheorem')
    source+=f"""theorem rational_curve {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    Group.OnCurve (RuntimeJubjub.d : F) (Elligator.rationalPoint (eval rho s) (eval rho t)) := by
  have sValue := Compiler.canonical_equal rho s (scaleLinear RuntimeElligatorAlgebra.k x) (by decide)
  have tValue := Compiler.canonical_equal rho t (scaleLinear RuntimeElligatorAlgebra.k y) (by decide)
  rw [eval_scale] at sValue tValue
  rw [sValue,tValue]
  exact RuntimeElligatorAlgebra.selected_root_on_curve (eval rho x) (eval rho y)
    (selected_root rho one four satisfied)
"""
    exports+=['first_coordinate','actual_cubic','qr_equation','cubic_nonzero','native_choice',
              'choice_value','selected_x','selected_y_squared','selected_square','selected_root','rational_curve']
    source+=''.join('#print axioms '+n+'\n' for n in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
