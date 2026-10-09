"""Derive the two meaningful routing flags from16 actual rows."""
from .generate_transfer_routing_zero_rows import _lc,_row
from .transfer_fixed_spend import canonical,combine


def generate(extraction):
    assert extraction['schema']=='shieldd-transfer-routing-meaningful-rows-v1'
    plan=extraction['plan'];chain=plan['chain'];one=((0,1),)
    reg,change,swap,zero,has_change=map(canonical,[plan[k] for k in ['regulated','change','swapped','zero','has_change']])
    sender=canonical(chain['sender']);first,second=map(canonical,plan['meaningful'])
    inverse=plan['inverse'];ip=inverse['certificate'];zp=plan['zero_product']
    products=[('inverse',change,canonical(inverse['inverse']),ip),('zero',change,zero,zp),
              ('regOr',reg,has_change,chain['regulator']),('firstOr',swap,sender,chain['first']),
              ('secondOr',combine(one,swap,-1),sender,chain['second'])]
    expected=[_row(terms,terms) for terms in [reg,swap,zero]]
    for label,left,right,data in products:
        auxiliary,output=map(canonical,[data['auxiliary'],data['output']])
        expected.extend([_row(combine(left,right,-1),auxiliary),
                         _row(combine(left,right),combine(auxiliary,tuple((c,4*v) for c,v in output)))])
        if label in ['inverse','zero']:
            assert len(data['rows'])==3
            target=has_change if label=='inverse' else ()
            expected.append(_row(combine(output,target,-1),()))
        else:assert len(data['rows'])==2
    rows=extraction['selected_rows'];assert len(rows)==16
    name='RuntimeRoutingMeaningful'
    source=('import ShielddSecurity.RowOrientationSoundness\nimport ShielddSecurity.RoutingPrecision\n'
            'set_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n'
            f'namespace ShielddSecurity.{name}\n')
    source+='def physicalIndices : List Nat := '+str([row['row'] for row in rows])+'\n'
    source+='def rawRows : List Row := [\n'+',\n'.join(_row(row['a'],row['b']) for row in rows)+']\n'
    source+='def expectedRows : List Row := [\n'+',\n'.join(expected)+']\n'
    for field,terms in [('regulated',reg),('change',change),('swapped',swap),('zeroFlag',zero),
                        ('hasChange',has_change),('senderMeaningful',sender),('firstMeaningful',first),
                        ('secondMeaningful',second),('inverse',inverse['inverse'])]:
        source+=f'def {field} : Linear := {_lc(terms)}\n'
    for label,left,right,data in products:
        source+=f'def {label}Output : Linear := {_lc(data["output"])}\n'
        source+=f'def {label}Aux : Linear := {_lc(data["auxiliary"])}\n'
    source+='''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem normalized (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho expectedRows := by
  have actual := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied (by decide)
  exact RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 rawRows)
    expectedRows (by decide) actual
private theorem hasChange_shape (rho : Nat → F) (one : rho 0 = 1) :
    eval rho hasChange = 1-eval rho zeroFlag := by
  have equation := Compiler.canonical_equal rho hasChange (Compiler.subtract [(0,1)] zeroFlag) (by decide)
  simpa only [Compiler.eval_subtract,eval,Int.cast_one,one_mul,add_zero,one] using equation
private theorem zero_equations (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho change * eval rho inverse = 1-eval rho zeroFlag ∧
    eval rho change * eval rho zeroFlag = 0 := by
  have rows := normalized rho satisfied
  have ip := Compiler.checked_product_sound rho expectedRows change inverse inverseOutput inverseAux four rows (by decide) (by decide)
  have ia := Compiler.checked_assertion_sound rho expectedRows inverseOutput hasChange rows (by decide)
  have zp := Compiler.checked_product_sound rho expectedRows change zeroFlag zeroOutput zeroAux four rows (by decide) (by decide)
  have za := Compiler.checked_assertion_sound rho expectedRows zeroOutput [] rows (by decide)
  exact ⟨ip.symm.trans (ia.trans (hasChange_shape rho one)),zp.symm.trans za⟩
theorem change_zero (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho zeroFlag = if eval rho change = 0 then 1 else 0 := by
  classical
  have equations := zero_equations rho one four satisfied
  exact RoutingPrecision.zero_test_sound _ _ _ equations.1 equations.2
theorem has_change (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho hasChange = if eval rho change = 0 then 0 else 1 := by
  classical
  rw [hasChange_shape rho one,change_zero rho one four satisfied]
  split <;> simp
theorem booleans (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    (eval rho regulated = 0 ∨ eval rho regulated = 1) ∧
    (eval rho swapped = 0 ∨ eval rho swapped = 1) := by
  have rows := normalized rho satisfied
  exact ⟨boolean_sound _ (Compiler.checked_row_sound rho expectedRows ⟨regulated,regulated⟩ rows (by decide)),
         boolean_sound _ (Compiler.checked_row_sound rho expectedRows ⟨swapped,swapped⟩ rows (by decide))⟩
theorem polynomials (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho senderMeaningful = eval rho regulated+eval rho hasChange-eval rho regulated*eval rho hasChange ∧
    eval rho firstMeaningful = eval rho swapped+eval rho senderMeaningful-eval rho swapped*eval rho senderMeaningful ∧
    eval rho secondMeaningful = (1-eval rho swapped)+eval rho senderMeaningful-(1-eval rho swapped)*eval rho senderMeaningful := by
  have rows := normalized rho satisfied
'''
    for label,left,right,_ in products[2:]:
        left_code='regulated' if label=='regOr' else 'swapped' if label=='firstOr' else '(Compiler.subtract [(0,1)] swapped)'
        right_code='hasChange' if label=='regOr' else 'senderMeaningful'
        target='senderMeaningful' if label=='regOr' else 'firstMeaningful' if label=='firstOr' else 'secondMeaningful'
        source+=f'''  have {label}Product := Compiler.checked_product_sound rho expectedRows {left_code} {right_code}
    {label}Output {label}Aux four rows (by decide) (by decide)
  have {label}Shape := Compiler.canonical_equal rho {target}
    (Compiler.subtract ({left_code} ++ {right_code}) {label}Output) (by decide)
  rw [Compiler.eval_subtract,eval_append,{label}Product] at {label}Shape
'''
    source+='''  have swapComplement : eval rho (Compiler.subtract [(0,1)] swapped) = 1-eval rho swapped := by
    simp only [Compiler.eval_subtract,eval,Int.cast_one,one_mul,add_zero,one]
  rw [swapComplement] at secondOrShape
  exact ⟨regOrShape,firstOrShape,secondOrShape⟩
def bit (flag : Bool) : F := if flag then 1 else 0
private theorem or_value (first second : Bool) :
    (bit first : F)+bit second-bit first*bit second = bit (first || second) := by
  cases first <;> cases second <;> simp [bit]
theorem flags_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ regulatedFlag swappedFlag : Bool,
      eval rho regulated = bit regulatedFlag ∧ eval rho swapped = bit swappedFlag ∧
      eval rho firstMeaningful = bit (swappedFlag || (regulatedFlag || decide (eval rho change ≠ 0))) ∧
      eval rho secondMeaningful = bit ((!swappedFlag) || (regulatedFlag || decide (eval rho change ≠ 0))) := by
  classical
  have checked := booleans rho satisfied
  obtain ⟨r,regulatedValue⟩ : ∃ flag : Bool, eval rho regulated = bit flag := by
    rcases checked.1 with zero | unit
    · exact ⟨false,by simpa [bit] using zero⟩
    · exact ⟨true,by simpa [bit] using unit⟩
  obtain ⟨s,swappedValue⟩ : ∃ flag : Bool, eval rho swapped = bit flag := by
    rcases checked.2 with zero | unit
    · exact ⟨false,by simpa [bit] using zero⟩
    · exact ⟨true,by simpa [bit] using unit⟩
  have changeValue : eval rho hasChange = bit (decide (eval rho change ≠ 0)) := by
    rw [has_change rho one four satisfied]
    by_cases empty : eval rho change = 0 <;> simp [bit,empty]
  have equations := polynomials rho one four satisfied
  have senderValue : eval rho senderMeaningful = bit (r || decide (eval rho change ≠ 0)) := by
    rw [equations.1,regulatedValue,changeValue]
    exact or_value _ _
  have complement : (1 : F)-bit s = bit (!s) := by cases s <;> simp [bit]
  refine ⟨r,s,regulatedValue,swappedValue,?_,?_⟩
  · rw [equations.2.1,swappedValue,senderValue]
    exact or_value _ _
  · rw [equations.2.2,swappedValue,senderValue,complement]
    exact or_value _ _
'''
    for export in ['change_zero','has_change','booleans','polynomials','flags_sound']:
        source+=f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
    return {name:source+f'end ShielddSecurity.{name}\n'}
