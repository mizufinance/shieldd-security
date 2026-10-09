"""Finite adapters to the universal ordinary-window constructor.

The existing strict EPK observer/row ingress remains the sole acceptance path.
This alternative does not alter the qualified folded first window or default
renderers. Its local result proves rows/curve/preservation; weighted native
table recurrence and six-scope publication remain separate joins.
"""
from . import generate_transfer_epk_fixed_completion as ingress
from . import generate_transfer_fixed_spend as renderer
from . import transfer_fixed_spend as fixed, transfer_relation as relation
from .generate_hash_round import linear, signed


def generate_window(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
                    scope_id,page_index=0,window_offset=0,*,readonly_lcs=()):
    checked,raw,normalized,_,_,plan,stem=ingress._selection(qualified_parent,raw_pages,
        accepted_capsules,accepted_roles,extracted,scope_id,page_index,window_offset,readonly_lcs)
    return render_checked(checked,raw,normalized,plan,window_offset,stem=stem)


def _layout(checked,raw,normalized,plan,offset):
    if type(offset)is not int or not 0<=offset<plan['window_count']:
        raise relation.RelationError('EPK template exact bounded window offset')
    window=plan['windows'][offset];stages=window['stages'];index=window['index']
    if index==0 or [s['kind'] for s in stages]!=['product']*6+['quotient']*2:
        raise relation.RelationError('EPK template requires ordinary six-product/two-quotient window')
    before,selected,after=checked['points'][offset];copy=checked['metadata']['constant_copy']
    handles=checked['metadata']['bits'][2*index:2*index+2]
    bits=[checked['observed'][fixed.source_index(ref)] for ref in handles]
    roles={role:(left,right,value) for role,left,right,value in checked['products']}
    values=[roles[f'window.{index}.{name}'][2] for name in ('xx','yy','sum','xy')]
    # Preserve the identical actual surrounding consumer frame used by the
    # existing neutral renderer, including every earlier selected physical row.
    kept=set(plan['kept']);prior=set(plan['initial_rows'])
    for previous in plan['windows'][:offset]:
        prior.update(row for step in previous['stages'] for row in step['rows'])
    for row in prior:
        for side in normalized[row]:kept.update(column for column,_ in side)
    copy_rows=[i for i,row in raw.items() if row==(fixed.canonical([(0,1),(copy,-1)]),())]
    if len(copy_rows)!=1:raise relation.RelationError('EPK template exact physical constant link')
    used={copy_rows[0]}
    for step in stages:used.update(step['rows'])
    for bit in bits:
        candidates=[i for i,row in normalized.items() if row==(bit,bit)]
        if len(candidates)!=1:raise relation.RelationError('EPK template unique actual bit row')
        used.add(candidates[0])
    writes=set()
    for step in stages:
        owned=({step['output'],step['auxiliary']} if step['kind']=='product' else
               {step['quotient'],step['product'],step['auxiliary']})
        if len(owned)!=(2 if step['kind']=='product' else 3) or owned&(writes|kept):
            raise relation.RelationError('EPK template actual fresh writes/kept alias')
        writes.update(owned)
    return dict(index=index,stages=stages,before=before,selected=selected,after=after,bits=bits,
                values=values,table=checked['tables'][offset],copy=copy,kept=sorted(kept),used=sorted(used))


def render_checked(checked,raw,normalized,plan,window_offset=0,*,stem):
    """Render only already accepted EPK rows, preserving exact physical indices."""
    layout=_layout(checked,raw,normalized,plan,window_offset)
    steps=layout['stages'];copy=layout['copy'];ns=stem+'TemplateCompletion'
    bindings=dict(zip(('inputX','inputY','selectedX','selectedY'),
                      (*layout['before'],*layout['selected'])))
    bindings.update(zip(('low','high'),layout['bits']))
    bindings.update(zip(('xx','yy','sum','xy'),layout['values']))
    out=['import ShielddSecurity.GroupFixedWindowTemplate\n',f'namespace ShielddSecurity.{ns}\n',
         'set_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n',
         f'def modulus : Nat := {relation.MODULUS}\ndef copyColumn : Nat := {copy}\n',
         f'def originalRows : List Nat := {layout["used"]}\n',
         f'def kept : List Nat := {layout["kept"]}\n',
         'def layout : GroupFixedWindowTemplate.Layout where\n']
    out += [f'  {key} := {linear(value)}\n' for key,value in bindings.items()]
    for key,point in zip(('base','twice','triple'),layout['table'][:3]):
        out.append(f'  {key} := ⟨{signed(point[0])},{signed(point[1])}⟩\n')
    out.append(f'  d := {signed(fixed.D)}\n')
    out.append('def products : GroupFixedWindowTemplate.ProductData where\n')
    for key,step in zip(('selectX','selectY','xx','yy','sum','xy'),steps[:6]):
        out.append(f'  {key} := .product [({step["auxiliary"]},1)]\n')
    encoded=[]
    for step in steps[:6]:
        encoded.append('.product '+ ' '.join(linear(step[key]) for key in ('left','right','remainder'))+
                       f' {step["output"]} {step["auxiliary"]}')
    out.append('def stages : List CompilerCompletion.Step := ['+','.join(encoded)+']\n')
    for key,step in zip(('x','y'),steps[6:]):
        out.append(f'def {key} : GroupQuotientPairCompletion.Coordinate where\n')
        out += [f'  {target} := {linear(step[source])}\n' for target,source in
                (('numerator','numerator'),('denominator','denominator'),('remainder','remainder'))]
        out += [f'  {target} := {step[source]}\n' for target,source in
                (('output','quotient'),('product','product'),('auxiliary','auxiliary'))]
    out.append('def rawRows : List Row := ['+',\n'.join(
        '⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in layout['used'])+']\n')
    out.append('''def expectedRows : List Row := CompilerCompletion.emitted stages ++
  GroupQuotientPairCompletion.rows x y ++ [⟨layout.low,layout.low⟩,⟨layout.high,layout.high⟩,⟨[],[]⟩]
def completeAssignment {F : Type} [Field F] (base : Nat → F) :=
  GroupFixedWindowTemplate.construct base stages x y
theorem checked_products : GroupFixedWindowTemplate.checkProducts modulus
    (CompilerCompletion.emitted stages) (layout.products products) = true := by decide

private theorem checked_terms (terms : Linear) (property : Nat → Prop) [DecidablePred property]
    (checked : terms.all (fun term => decide (property term.1)) = true) :
    ∀ term ∈ terms, property term.1 := by
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)

private theorem shape_x : x.Shape := by
  refine ⟨by decide,by decide,by decide,?_⟩
  exact checked_terms x.inputs (fun column => column ∉ x.writes) (by decide)
private theorem shape_y : y.Shape := by
  refine ⟨by decide,by decide,by decide,?_⟩
  exact checked_terms y.inputs (fun column => column ∉ y.writes) (by decide)

theorem actual_window_complete {F : Type} [Field F] [CharP F modulus]
    (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base copyColumn = base 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (layout.d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (low high : Bool) (lowValue : eval base layout.low = if low then 1 else 0)
    (highValue : eval base layout.high = if high then 1 else 0)
    (inputValid : Group.OnCurve (layout.d : F) (layout.input base)) :
    Satisfies (completeAssignment base) rawRows ∧
      Group.OnCurve (layout.d : F) (GroupQuotientPairCompletion.point x y (completeAssignment base)) ∧
      (∀ column ∈ kept, completeAssignment base column = base column) ∧
      GroupQuotientPairCompletion.point x y (completeAssignment base) =
        Group.affineAdd (layout.d : F) (layout.input base)
          (Group.windowPoint (if low then 1 else 0) (if high then 1 else 0)
            (GroupFixedWindowTemplate.castPoint layout.base)
            (GroupFixedWindowTemplate.castPoint layout.twice)
            (GroupFixedWindowTemplate.castPoint layout.triple)) := by
  have inputsKept : ∀ term ∈ layout.inputX ++ layout.inputY ++ layout.low ++ layout.high, term.1 ∈ kept :=
    checked_terms (layout.inputX ++ layout.inputY ++ layout.low ++ layout.high)
      (fun column => column ∈ kept) (by decide)
  have prefixFresh : ∀ row ∈ CompilerCompletion.emitted stages, ∀ term ∈ row.a ++ row.b,
      term.1 ∉ x.writes ∧ term.1 ∉ y.writes := by
    intro row member
    have checked : (CompilerCompletion.emitted stages).all (fun row => (row.a ++ row.b).all
        (fun term => decide (term.1 ∉ x.writes ∧ term.1 ∉ y.writes))) = true := by decide
    exact checked_terms (row.a ++ row.b)
      (fun column => column ∉ x.writes ∧ column ∉ y.writes)
      (List.all_eq_true.mp checked row member)
  have quotientKept : ∀ column ∈ kept, column ∉ x.writes ∧ column ∉ y.writes := by
    intro column member
    have checked : kept.all (fun column => decide (column ∉ x.writes ∧ column ∉ y.writes)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp checked column member)
  have secondFresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes := by
    intro row member
    have checked : x.rows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (term.1 ∉ y.writes))) = true := by decide
    exact checked_terms (row.a ++ row.b) (fun column => column ∉ y.writes)
      (List.all_eq_true.mp checked row member)
  have done := GroupFixedWindowTemplate.construct_complete layout products stages kept base
    (CompilerOrder.checked_order kept [] stages (by decide))
    (by simp only [stages,ScalarRandomizerCompletion.Products]) checked_products (by decide) inputsKept
    one four imaginary nonSquare imaginarySquare low high lowValue highValue inputValid
    (GroupFixedWindowTemplate.checked_table_curve layout.d layout.base base one (by decide))
    (GroupFixedWindowTemplate.checked_table_curve layout.d layout.twice base one (by decide))
    (GroupFixedWindowTemplate.checked_table_curve layout.d layout.triple base one (by decide))
    x y shape_x shape_y (checked_terms y.inputs (fun column => column ∉ x.writes) (by decide))
    secondFresh (by decide)
    prefixFresh quotientKept (by decide)
  have bitsSame (terms : Linear) (included : ∀ term ∈ terms, term ∈ layout.low ++ layout.high) :
      eval (completeAssignment base) terms = eval base terms := by
    apply eval_agrees
    intro term member
    apply done.2.2.1 term.1
    apply inputsKept term
    rcases List.mem_append.mp (included term member) with inLow | inHigh
    · exact List.mem_append_left layout.high (List.mem_append_right _ inLow)
    · exact List.mem_append_right _ inHigh
  have lowBuilt := (bitsSame layout.low (by intro term member; exact List.mem_append_left _ member)).trans lowValue
  have highBuilt := (bitsSame layout.high (by intro term member; exact List.mem_append_right _ member)).trans highValue
  have extras : Satisfies (completeAssignment base)
      [⟨layout.low,layout.low⟩,⟨layout.high,layout.high⟩,⟨[],[]⟩] := by
    intro row member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change Square (eval (completeAssignment base) layout.low) (eval (completeAssignment base) layout.low)
      rw [lowBuilt]; cases low <;> simp [Square]
    · change Square (eval (completeAssignment base) layout.high) (eval (completeAssignment base) layout.high)
      rw [highBuilt]; cases high <;> simp [Square]
    · simp [Square,eval]
  have expected : Satisfies (completeAssignment base) expectedRows := by
    intro row member
    simp only [expectedRows,List.append_assoc] at member
    rcases List.mem_append.mp member with prefixRows | remaining
    · exact done.1 row (List.mem_append_left _ prefixRows)
    · rcases List.mem_append.mp remaining with quotientRows | extra
      · exact done.1 row (List.mem_append_right _ quotientRows)
      · exact extras row extra
  have copyLink : completeAssignment base copyColumn = completeAssignment base 0 := by
    change GroupFixedWindowTemplate.construct base stages x y copyColumn =
      GroupFixedWindowTemplate.construct base stages x y 0
    rw [done.2.2.1 copyColumn (by decide),done.2.2.1 0 (by decide),linked]
  have coverage : rawRows.all (fun actual => expectedRows.any (fun modeled => decide
      (Compiler.canonical modulus (Compiler.unoutline copyColumn actual.a) = Compiler.canonical modulus modeled.a ∧
       Compiler.canonical modulus (Compiler.unoutline copyColumn actual.b) = Compiler.canonical modulus modeled.b))) = true := by decide
  refine ⟨?_,done.2.1,done.2.2.1,done.2.2.2⟩
  intro actual member
  obtain ⟨modeled,present,equal⟩ := List.any_eq_true.mp (List.all_eq_true.mp coverage actual member)
  have pair := of_decide_eq_true equal
  have satisfied := expected modeled present
  rw [← Compiler.canonical_equal (completeAssignment base) _ _ pair.1,
      ← Compiler.canonical_equal (completeAssignment base) _ _ pair.2] at satisfied
  simpa only [Compiler.eval_unoutline _ copyColumn _ copyLink] using satisfied
''')
    out.append(f'end ShielddSecurity.{ns}\n')
    source=''.join(out)
    source=source.replace(f'end ShielddSecurity.{ns}',
        '#print axioms checked_products\n#print axioms actual_window_complete\n'+f'end ShielddSecurity.{ns}')
    return renderer._signature_audits(source)
