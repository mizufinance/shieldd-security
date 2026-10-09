"""One finite physical ordering/active prefix proof module per routing bit."""
from .generate_transfer_routing_zero_rows import _lc,_row
from .transfer_fixed_spend import canonical,combine


def generate(extraction):
    assert extraction['schema']=='shieldd-transfer-routing-order-active-rows-v1'
    raw={row['row']:row for row in extraction['selected_rows']}
    plan=extraction['plan'];result={};one=((0,1),)
    regulated=canonical(plan['regulated'])
    for step in plan['steps']:
        index=step['index'];assert 0<=index<32
        name=f'RuntimeRoutingOrderActive{index:02}'
        first,second,active=map(canonical,[step['regulated_prefix'],step['unregulated_prefix'],step['active']])
        order,select=step['ordering'],step['select']
        order_right=combine(one,second,-1);select_right=combine(first,second,-1)
        expected=[]
        for left,right,data in [(first,order_right,order),(regulated,select_right,select)]:
            auxiliary=canonical(data['auxiliary']);output=canonical(data['output'])
            expected.extend([_row(combine(left,right,-1),auxiliary),
                             _row(combine(left,right),combine(auxiliary,tuple((c,4*v) for c,v in output)))])
        expected.extend([_row(canonical(order['output']),()),_row(regulated,regulated),_row(active,active)])
        indices=[*order['rows'],*select['rows'],step['boolean_row'],plan['regulated_boolean'],plan['constant_link']]
        assert len(indices)==len(set(indices))==8
        source=('import ShielddSecurity.RowOrientationSoundness\nimport ShielddSecurity.RoutingPrecision\n'
                'set_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n'
                f'namespace ShielddSecurity.{name}\n')
        source+='def physicalIndices : List Nat := '+str(indices)+'\n'
        source+='def rawRows : List Row := [\n'+',\n'.join(_row(raw[i]['a'],raw[i]['b']) for i in indices)+']\n'
        source+='def expectedRows : List Row := [\n'+',\n'.join(expected)+']\n'
        for field,terms in [('regulated',regulated),('first',first),('second',second),('active',active),
                            ('orderOutput',order['output']),('orderAux',order['auxiliary']),
                            ('selectOutput',select['output']),('selectAux',select['auxiliary'])]:
            source+=f'def {field} : Linear := {_lc(terms)}\n'
        source+='''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem normalized (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho expectedRows := by
  have actual := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied (by decide)
  exact RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows 200692 rawRows)
    expectedRows (by decide) actual
theorem order_sound (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho first * (1-eval rho second) = 0 := by
  have rows := normalized rho satisfied
  have product := Compiler.checked_product_sound rho expectedRows first
    (Compiler.subtract [(0,1)] second) orderOutput orderAux four rows (by decide) (by decide)
  have assertion := Compiler.checked_assertion_sound rho expectedRows orderOutput [] rows (by decide)
  have meaning : eval rho (Compiler.subtract [(0,1)] second) = 1-eval rho second := by
    simp only [Compiler.eval_subtract,eval,Int.cast_one,one_mul,add_zero,one]
  rw [meaning] at product
  exact product.symm.trans assertion
theorem active_sound (rho : Nat → F) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho active = eval rho second + eval rho regulated * (eval rho first-eval rho second) := by
  have rows := normalized rho satisfied
  have product := Compiler.checked_product_sound rho expectedRows regulated
    (Compiler.subtract first second) selectOutput selectAux four rows (by decide) (by decide)
  have shape : Compiler.canonical Scalar.modulus active =
      Compiler.canonical Scalar.modulus (second ++ selectOutput) := by decide
  have selected := Compiler.canonical_equal rho active (second ++ selectOutput) shape
  rw [eval_append,product,Compiler.eval_subtract] at selected
  exact selected
theorem booleans_sound (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Square (eval rho regulated) (eval rho regulated) ∧ Square (eval rho active) (eval rho active) := by
  have rows := normalized rho satisfied
  exact ⟨Compiler.checked_row_sound rho expectedRows ⟨regulated,regulated⟩ rows (by decide),
    Compiler.checked_row_sound rho expectedRows ⟨active,active⟩ rows (by decide)⟩
'''
        for export in ['order_sound','active_sound','booleans_sound']:
            source+=f'set_option pp.all true in\n#check @{export}\n#print axioms {export}\n'
        result[name]=source+f'end ShielddSecurity.{name}\n'
    assert len(result)==32
    return result
