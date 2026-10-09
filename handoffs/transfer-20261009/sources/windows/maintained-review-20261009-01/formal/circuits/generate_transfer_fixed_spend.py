"""Finite actual-row fixed-spend candidates; never write evidence or qualify.

Each window retains captured LCs, exact original row indices, native table
constants and independent local equations. Kernel checks remain mandatory.
"""
from . import transfer_fixed_spend as fixed, transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index
from .generate_hash_round import linear, signed, _signature_audits
from .transfer_ownership import generate_quotient_boundaries
from .transfer_arithmetic import completion_certificate, product_completion_certificate


def _product_completion_sources(prefix, left, right, output, certificate, raw, normalized, copy):
    """Construct only the actual fresh product pivot and square auxiliary."""
    c=product_completion_certificate(left,right,output,certificate,normalized)
    if c is None:return '',[]
    pivot,auxiliary=c['output'],c['auxiliary']
    left,right,remainder=(linear(c[key]) for key in ('left','right','remainder'))
    rows='['+', '.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in c['rows'])+']'
    step=f'.product {left} {right} {remainder} {pivot} {auxiliary}'
    expected=[f'⟨Compiler.subtract {left} {right},[({auxiliary},1)]⟩',
              f'⟨{left} ++ {right},[({auxiliary},1)] ++ scaleLinear 4 ([({pivot},1)] ++ {remainder})⟩']
    out=[f'def {prefix}ProductOriginalRows : List Nat := {c["rows"]}\n',
         f'def {prefix}ProductRows : List Row := {rows}\n',
         f'def {prefix}ProductSteps : List CompilerCompletion.Step := [{step}]\n',
         f'''theorem {prefix}_product_ordered : CompilerCompletion.Topological [0,{copy}] [] {prefix}ProductSteps := by
  simp [{prefix}ProductSteps, CompilerCompletion.Topological, CompilerCompletion.Step.Shape,
    CompilerCompletion.Step.writes]
theorem {prefix}_product_coverage : ∀ actual ∈ {prefix}ProductRows, ∃ expected ∈
    CompilerCompletion.emitted {prefix}ProductSteps,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [{prefix}ProductRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
''']
    for row in expected:
        out.append(f'''  · refine ⟨{row}, ?_, by decide, by decide⟩
    simp [{prefix}ProductSteps,CompilerCompletion.emitted,CompilerCompletion.Step.rows,ScalarCompletion.productRows]
''')
    out.append(f'''theorem complete_{prefix} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (linked : rho {copy} = rho 0) :
    Satisfies (ScalarCompletion.extendProduct rho {left} {right} {remainder} {pivot} {auxiliary})
      {prefix}ProductRows := by
  have completed := CompilerCompletion.original_rows_complete rho {prefix}ProductSteps [0,{copy}]
    {prefix}ProductRows {copy} {prefix}_product_ordered (by exact ⟨True.intro,True.intro⟩)
    (by decide) (by decide) linked {prefix}_product_coverage
  simpa only [{prefix}ProductSteps,CompilerCompletion.run,CompilerCompletion.Step.run] using completed.1
''')
    return ''.join(out),[prefix+'_product_ordered',prefix+'_product_coverage','complete_'+prefix]


def _completion_sources(certificates, raw, normalized, copy):
    out=[];names=[]
    for axis,certificate in enumerate(certificates):
        c=completion_certificate(certificate,normalized)
        if c is None:continue
        q,p,a=(c[key] for key in ('quotient','product','auxiliary'))
        n,d,r=(linear(c[key]) for key in ('numerator','denominator','remainder'))
        prefix=f'quotient{axis}'
        out.append(f'def {prefix}OriginalRows : List Nat := {c["rows"]}\n')
        out.append(f'def {prefix}Rows : List Row := ['+', '.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in c['rows'])+']\n')
        expected=[f'⟨Compiler.subtract [({q},1)] {d},[({a},1)]⟩',
                  f'⟨[({q},1)] ++ {d},[({a},1)] ++ scaleLinear 4 ([({p},1)] ++ {r})⟩',
                  f'⟨Compiler.subtract ([({p},1)] ++ {r}) {n},[]⟩']
        out.append(f'''theorem {prefix}_coverage : ∀ actual ∈ {prefix}Rows, ∃ expected ∈
    GroupRowCompletion.quotientRows {n} {d} {r} {q} {p} {a},
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [{prefix}Rows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
''')
        for row in expected:
            out.append(f'''  · refine ⟨{row}, ?_, by decide, by decide⟩
    simp [GroupRowCompletion.quotientRows,ScalarCompletion.productRows]
''')
        out.append(f'''theorem complete_quotient{axis} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (linked : rho {copy} = rho 0) (legal : eval rho {d} ≠ 0) :
    Satisfies (GroupRowCompletion.extendQuotient rho {n} {d} {r} {q} {p} {a}) {prefix}Rows := by
  exact GroupRowCompletion.original_rows_complete rho {n} {d} {r} {q} {p} {a}
    (by decide) (by decide) (by decide) (by simp [GroupRowCompletion.writes]) legal {prefix}Rows {copy}
    (by decide) (by decide) linked {prefix}_coverage
''')
        names += [prefix+'_coverage','complete_quotient'+str(axis)]
    return ''.join(out),names


def generate_window_completion(data, accepted_roles, extracted, window_offset=0):
    """Compose <=8 actual owned stages, retaining all earlier row supports.

    Nonzero denominators are local construction inputs here. Whole-loop
    completeness must derive them from the constructed selector/input curve
    semantics; this candidate does not promote that independent obligation.
    """
    plan=fixed.fixed_completion_plan(data,accepted_roles,extracted)
    checked,raw,normalized,*_=fixed._selection(data,accepted_roles,extracted)
    return render_window_completion(checked,raw,normalized,plan,window_offset)


def render_window_completion(checked,raw,normalized,plan,window_offset=0,*,stem=None):
    """Render a separately checked exact fixed-window construction plan.

    Typed ingress owns source/role/row acceptance. This neutral renderer does
    not accept a spend schema on behalf of another native caller.
    """
    if type(window_offset)!=int or not 0<=window_offset<plan['window_count']:
        raise relation.RelationError('fixed completion window offset')
    window=plan['windows'][window_offset];copy=checked['metadata']['constant_copy']
    kept=set(plan['kept']);prior_rows=set(plan['initial_rows'])
    for previous in plan['windows'][:window_offset]:
        prior_rows.update(row for stage in previous['stages'] for row in stage['rows'])
    for row in prior_rows:
        for side in normalized[row]:kept.update(column for column,_ in side)
    stages=window['stages'];terms=[];expected={};definitions=[]
    product_count=sum(stage['kind']=='product' for stage in stages)
    for ordinal,stage in enumerate(stages):
        if stage['kind']=='product':
            left,right,remainder=(linear(stage[key]) for key in ('left','right','remainder'))
            output,auxiliary=stage['output'],stage['auxiliary']
            terms.append(f'.compiler (.product {left} {right} {remainder} {output} {auxiliary})')
            rows=[f'⟨Compiler.subtract {left} {right},[({auxiliary},1)]⟩',
                  f'⟨{left} ++ {right},[({auxiliary},1)] ++ scaleLinear 4 ([({output},1)] ++ {remainder})⟩']
        elif stage['kind']=='linear':
            input_lc,remainder=(linear(stage[key]) for key in ('input','remainder'))
            output=stage['output'];terms.append(f'.linear {input_lc} {remainder} {output}')
            rows=[f'⟨Compiler.subtract ([({output},1)] ++ {remainder}) {input_lc},[]⟩']
        else:
            axis=ordinal-product_count
            n,d,r=(linear(stage[key]) for key in ('numerator','denominator','remainder'))
            q,p,a=(stage[key] for key in ('quotient','product','auxiliary'))
            definitions.extend((f'def numerator{axis} : Linear := {n}\n',
                                f'def denominator{axis} : Linear := {d}\n',
                                f'def remainder{axis} : Linear := {r}\n'))
            terms.append(f'.quotient numerator{axis} denominator{axis} remainder{axis} {q} {p} {a}')
            rows=[f'⟨Compiler.subtract [({q},1)] {d},[({a},1)]⟩',
                  f'⟨[({q},1)] ++ {d},[({a},1)] ++ scaleLinear 4 ([({p},1)] ++ {r})⟩',
                  f'⟨Compiler.subtract ([({p},1)] ++ {r}) {n},[]⟩']
        expected.update(zip(stage['rows'],rows))
    constant=next(i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),()))
    expected[constant]='⟨[],[]⟩';indices=sorted(expected)
    ns=(stem or f'RuntimeFixedSpendWindow{window["index"]:03d}')+'Completion'
    definition_names=['kept','completionSteps','productStages','CompilerLinearCompletion.rows',
                      'numerator0','denominator0','remainder0','numerator1','denominator1','remainder1']
    if not any(stage['kind']=='quotient' for stage in stages):definition_names=definition_names[:-6]
    out=['import ShielddSecurity.GroupCircuitOrder\n',f'namespace ShielddSecurity.{ns}\n',
         'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
         f'-- Actual metadata {checked["metadata_sha256"]}; exact relation {checked["metadata"]["relation_digest"]}.\n',
         '-- Local ownership/completion candidate; whole-loop denominator/native/caller joins remain separate.\n',
         f'def modulus : Nat := {relation.MODULUS}\ndef kept : List Nat := {sorted(kept)}\n',
         f'def originalRows : List Nat := {indices}\n',
         'def rawRows : List Row := ['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in indices)+']\n',
         *definitions,'def productStages : List GroupCircuitCompletion.Step := ['+','.join(terms[:product_count])+']\n',
         'def completionSteps : List GroupCircuitCompletion.Step := productStages ++ ['+
         ','.join(terms[product_count:]+['.compiler (.equal [] [])'])+']\n',
         '''def productAssignment {F : Type} [Field F] (rho : Nat → F) := GroupCircuitCompletion.run rho productStages
def completeAssignment {F : Type} [Field F] (rho : Nat → F) := GroupCircuitCompletion.run rho completionSteps
theorem completion_ordered : GroupCircuitCompletion.Topological kept [] completionSteps := by
  exact GroupCircuitOrder.checked_order kept [] completionSteps (by decide)
''']
    quotients=[stage for stage in stages if stage['kind']=='quotient']
    legal_parameters=''
    if quotients:
        if len(quotients)!=2:raise relation.RelationError('fixed completion mixed folded/nonfolded quotient boundary')
        first=quotients[0]
        extension=f'GroupRowCompletion.extendQuotient (productAssignment rho) numerator0 denominator0 remainder0 {first["quotient"]} {first["product"]} {first["auxiliary"]}'
        out.append(f'''theorem denominator_preserved {{F : Type}} [Field F] (rho : Nat → F) :
    eval ({extension}) denominator1 = eval (productAssignment rho) denominator1 :=
  GroupRowCompletion.eval_preserves (productAssignment rho) numerator0 denominator0 remainder0 denominator1
    {first['quotient']} {first['product']} {first['auxiliary']} (by simp [denominator1,GroupRowCompletion.writes])
''')
        legal_parameters='\n    (legalX : eval (productAssignment rho) denominator0 ≠ 0)\n    (legalY : eval (productAssignment rho) denominator1 ≠ 0)'
        out.append(f'''theorem completion_legal {{F : Type}} [Field F] (rho : Nat → F){legal_parameters} :
    GroupCircuitCompletion.Legal rho completionSteps := by
  change '''+'True ∧ '*product_count+f'''(eval (productAssignment rho) denominator0 ≠ 0) ∧
    (eval ({extension}) denominator1 ≠ 0) ∧
    (eval (completeAssignment rho) [] = eval (completeAssignment rho) []) ∧ True
  refine ⟨'''+','.join(['True.intro']*product_count+['legalX','?_', 'rfl','True.intro'])+'''⟩
  rw [denominator_preserved]
  exact legalY
''')
    else:
        out.append('''theorem completion_legal {F : Type} [Field F] (rho : Nat → F) :
    GroupCircuitCompletion.Legal rho completionSteps := by
  simp [completionSteps, productStages, GroupCircuitCompletion.Legal, GroupCircuitCompletion.Step.Legal,
    CompilerCompletion.Step.Legal]
''')
    out.append(f'''theorem original_coverage : ∀ actual ∈ rawRows, ∃ expected ∈ GroupCircuitCompletion.emitted completionSteps,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in indices)+'\n')
    for index in indices:
        out.append(f'''  · refine ⟨{expected[index]}, ?_, by decide, by decide⟩
    simp ['''+', '.join(definition_names)+''', GroupCircuitCompletion.emitted, GroupCircuitCompletion.Step.rows,
      CompilerCompletion.Step.rows, ScalarCompletion.productRows, GroupRowCompletion.quotientRows,
      Compiler.subtract, scaleLinear]
''')
    out.append(f'''theorem local_rows_complete {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (linked : rho {copy} = rho 0){legal_parameters} :
    Satisfies (completeAssignment rho) rawRows ∧
      (∀ column ∈ kept, completeAssignment rho column = rho column) :=
  GroupCircuitCompletion.original_rows_complete rho completionSteps kept rawRows {copy}
    completion_ordered (completion_legal rho'''+(' legalX legalY' if quotients else '')+''')
    (by decide) (by decide) linked original_coverage
''')
    audits=['completion_ordered','completion_legal','original_coverage','local_rows_complete']
    if quotients:audits.insert(1,'denominator_preserved')
    out.extend('#print axioms '+name+'\n' for name in audits)
    out.append(f'end ShielddSecurity.{ns}\n')
    return _signature_audits(''.join(out))


def generate_randomizer_order(data, accepted_roles, extracted):
    """Bounded exact product ownership, composed over the symbolic bit footprint.

    This candidate proves ordering only. Canonical input meaning, constructed
    row coverage and the endpoint/native/caller joins remain separate proofs.
    """
    plan=fixed.randomizer_completion_plan(data,accepted_roles,extracted)
    return render_randomizer_order(plan)


def _kept_blocks(plan, block_size):
    if block_size is None:
        return None
    if type(block_size) is not int or not 1 <= block_size <= 256:
        raise relation.RelationError('bounded protected column blocks require size1..256')
    kept = plan['kept']
    if not kept or any(type(column) is not int or column < 0 for column in kept) or len(set(kept)) != len(kept):
        raise relation.RelationError('exact unique protected column inventory')
    return [kept[index:index+block_size] for index in range(0,len(kept),block_size)]


def _kept_membership(blocks, column, qualifier):
    selected = next((index for index,block in enumerate(blocks) if column in block),None)
    if selected is None:
        raise relation.RelationError('required protected column absent')
    proof = '(by decide)'
    for index in range(len(blocks)-2,-1,-1):
        if selected == index:
            proof = f'(List.mem_append_left _ {proof})'
        elif selected > index:
            proof = f'(List.mem_append_right _ {proof})'
    return f'(by change {column} ∈ '+_kept_expression(blocks,qualifier)+f'; exact {proof})'


def _kept_expression(blocks,qualifier=''):
    value=f'{qualifier}keptPart{len(blocks)-1:03d}'
    for index in range(len(blocks)-2,-1,-1):
        value=f'({qualifier}keptPart{index:03d} ++ {value})'
    return value


def _kept_property(blocks,lower,upper,part_stem,qualifier=''):
    property=f'(fun column => column < {lower} ∨ {upper} ≤ column)'
    proof=f'{part_stem}{len(blocks)-1:03d}'
    for index in range(len(blocks)-2,-1,-1):
        # Suffix names retain their original block indices.
        suffix=f'{qualifier}keptPart{len(blocks)-1:03d}'
        for tail in range(len(blocks)-2,index,-1):
            suffix=f'({qualifier}keptPart{tail:03d} ++ {suffix})'
        proof=f'(kept_append_property {qualifier}keptPart{index:03d} {suffix} {property} {part_stem}{index:03d} {proof})'
    return proof


_KEPT_APPEND_PROPERTY='''private theorem kept_append_property (left right : List Nat) (property : Nat → Prop)
    (first : ∀ column ∈ left, property column) (second : ∀ column ∈ right, property column) :
    ∀ column ∈ left ++ right, property column := by
  intro column member
  rcases List.mem_append.mp member with fromLeft | fromRight
  · exact first column fromLeft
  · exact second column fromRight
'''


def render_randomizer_order(plan,*,namespace='RuntimeFixedSpendRandomizerOrder',kept_block_size=None):
    """Neutral bounded order renderer for a separately checked252-bit plan."""
    chunks=plan['chunks'];lower=chunks[0][0]['output']
    if not (plan['value']<lower and plan['bit_start']+252<=lower):
        raise relation.RelationError('randomizer initial footprint exceeds first product bound')
    for chunk in chunks:
        for stage in chunk:
            if not (lower<=stage['output']<stage['auxiliary'] and
                    all(column<stage['output'] for key in ('left','right','remainder') for column,_ in stage[key])):
                raise relation.RelationError('randomizer product support is not bounded in captured order')
            lower=stage['auxiliary']+1
    first=chunks[0][0]['output'];ns=namespace;blocks=_kept_blocks(plan,kept_block_size)
    kept_source=(f'def kept : List Nat := {plan["kept"]}\n' if blocks is None else
        ''.join(f'def keptPart{i:03d} : List Nat := {block}\n' for i,block in enumerate(blocks))+
        'def kept : List Nat := '+_kept_expression(blocks)+'\n')
    out=['import ShielddSecurity.ScalarRandomizerBounds\n',f'namespace ShielddSecurity.{ns}\n',
         'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
         '-- Exact retained product ownership only; no row/output truth is checked here.\n',
         kept_source,
         f'def initialRows : List Row := ScalarRandomizerCompletion.initialRows {plan["value"]} {plan["bit_start"]}\n',
         'def prefix000 : List CompilerCompletion.Step := []\n',
         'def prior000 : List Row := initialRows ++ CompilerCompletion.emitted prefix000\n',
         f'''theorem prior_bound000 : ScalarRandomizerBounds.RowsBelow {first} prior000 :=
  ScalarRandomizerBounds.initial_rows_below {plan['value']} {plan['bit_start']} {first} (by decide) (by decide)
theorem prefix_order000 : CompilerCompletion.Topological kept initialRows prefix000 := True.intro
theorem prefix_products000 : ScalarRandomizerCompletion.Products prefix000 := True.intro
''']
    if blocks is not None:
        final=chunks[-1][-1]['auxiliary']+1
        if any(first<=column<final for column in plan['kept']):
            raise relation.RelationError('protected columns overlap actual comparator write interval')
        out.append(_KEPT_APPEND_PROPERTY)
        out.append(''.join(f'''private theorem kept_outside_products{part:03d} :
    ∀ column ∈ keptPart{part:03d}, column < {first} ∨ {final} ≤ column := by
  have checked : keptPart{part:03d}.all
      (fun column => decide (column < {first} ∨ {final} ≤ column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
''' for part in range(len(blocks))))
        out.append(f'''private theorem kept_outside_products :
    ∀ column ∈ kept, column < {first} ∨ {final} ≤ column := by
  exact '''+_kept_property(blocks,first,final,'kept_outside_products')+'\n')
    lower=first
    for i,chunk in enumerate(chunks):
        index=f'{i:03d}';next_index=f'{i+1:03d}';upper=chunk[-1]['auxiliary']+1
        if blocks is None:
            protection=f'theorem checked_protected{index} : ScalarRandomizerBounds.checkProtected kept chunk{index} = true := by decide'
            certificate=f'(ScalarRandomizerBounds.protected_certificate kept chunk{index} checked_protected{index})'
        else:
            protection=f'''private theorem protection{index} :
    ∀ stage ∈ chunk{index}, ∀ column ∈ kept, column ∉ stage.writes := by
  intro stage member column present
  have checked : chunk{index}.all (fun step => step.writes.all
      (fun written => decide ({first} ≤ written ∧ written < {final}))) = true := by decide
  intro written
  have bounded : {first} ≤ column ∧ column < {final} := of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)
  have outside := kept_outside_products column present
  rcases outside with before | after <;> omega
'''
            certificate=f'protection{index}'
        terms=[f'.product {linear(stage["left"])} {linear(stage["right"])} {linear(stage["remainder"])} {stage["output"]} {stage["auxiliary"]}' for stage in chunk]
        out.append(f'''def chunk{index} : List CompilerCompletion.Step := ['''+','.join(terms)+f''']
def prefix{next_index} : List CompilerCompletion.Step := prefix{index} ++ chunk{index}
def prior{next_index} : List Row := initialRows ++ CompilerCompletion.emitted prefix{next_index}
theorem checked_bound{index} : ScalarRandomizerBounds.checkBounded {lower} {upper} chunk{index} = true := by decide
{protection}
theorem chunk_order{index} : CompilerCompletion.Topological kept prior{index} chunk{index} :=
  ScalarRandomizerBounds.bounded_ordered {lower} {upper} chunk{index} kept prior{index}
    checked_bound{index} prior_bound{index}
    {certificate}
theorem prefix_order{next_index} : CompilerCompletion.Topological kept initialRows prefix{next_index} :=
  ScalarRandomizerCompletion.ordered_append kept initialRows prefix{index} chunk{index}
    prefix_order{index} chunk_order{index}
theorem prior_bound{next_index} : ScalarRandomizerBounds.RowsBelow {upper} prior{next_index} := by
  simpa only [prior{next_index}, prefix{next_index}, prior{index},
    ScalarRandomizerBounds.emitted_append, List.append_assoc] using
    (ScalarRandomizerBounds.rows_append {upper} prior{index} (CompilerCompletion.emitted chunk{index})
      (ScalarRandomizerBounds.rows_mono {lower} {upper} prior{index} prior_bound{index} (by decide))
      (ScalarRandomizerBounds.bounded_rows {lower} {upper} chunk{index} checked_bound{index}))
theorem prefix_products{next_index} : ScalarRandomizerCompletion.Products prefix{next_index} :=
  ScalarRandomizerCompletion.products_append prefix{index} chunk{index} prefix_products{index}
    (by trivial)
''')
        lower=upper
    end=f'{len(chunks):03d}'
    out.append(f'''def allStages : List CompilerCompletion.Step := prefix{end}
theorem ordered : CompilerCompletion.Topological kept initialRows allStages := prefix_order{end}
theorem products : ScalarRandomizerCompletion.Products allStages := prefix_products{end}
theorem row_support : ScalarRandomizerBounds.RowsBelow {lower}
    (initialRows ++ CompilerCompletion.emitted allStages) := prior_bound{end}
''')
    out.extend('#print axioms '+name+'\n' for name in ('ordered','products','row_support'))
    out.append(f'end ShielddSecurity.{ns}\n')
    return _signature_audits(''.join(out))


def generate_randomizer_completion(data, accepted_roles, extracted):
    """Construct the real comparator from canonical input, without its endpoint assertion.

    Requires the separately generated order and randomizer interpretation
    modules for the SAME accepted metadata/retained row selection.
    """
    plan=fixed.randomizer_completion_plan(data,accepted_roles,extracted)
    return render_randomizer_completion(plan)


def render_randomizer_completion(plan,*,namespace='RuntimeFixedSpendRandomizerCompletion',
        order_namespace='RuntimeFixedSpendRandomizerOrder',sound_namespace='RuntimeTransferRandomizer',kept_block_size=None):
    """Neutral252-bit constructor; native integer seed precedes bit/row truth."""
    # Admit precisely the allocation supported by the symbolic bound proof.
    render_randomizer_order(plan,namespace=order_namespace,kept_block_size=kept_block_size)
    value,start=plan['value'],plan['bit_start'];count=len(plan['chunks'])
    ns=namespace
    out=[f'import ShielddSecurity.{order_namespace}\n',
         f'import ShielddSecurity.{sound_namespace}\n',
         f'namespace ShielddSecurity.{ns}\n',
         'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
         f'def rows : List Row := ScalarRandomizerCompletion.constructedRows {value} {start} O.allStages\n',
         '''private theorem boolean_included (columns : List Nat)
    (checked : columns.all (fun column => decide (column ∈ List.range' '''+str(start)+''' 252)) = true) :
    ∀ row ∈ columns.map booleanRow, row ∈ rows := by
  intro row member
  obtain ⟨column, inside, rfl⟩ := List.mem_map.mp member
  apply List.mem_append_left (CompilerCompletion.emitted O.allStages)
  apply List.mem_append_left _
  exact List.mem_map.mpr ⟨column,
    of_decide_eq_true (List.all_eq_true.mp checked column inside), rfl⟩
''']
    for i in range(count):
        index=f'{i:03d}'
        out.append(f'''private theorem product_included{index} :
    ∀ row ∈ CompilerCompletion.emitted O.chunk{index}, row ∈ rows := by
  intro row member
  apply List.mem_append_right _
  change row ∈ CompilerCompletion.emitted O.prefix{count:03d}
''')
        for k in range(count,i,-1):
            out.append(f'  rw [O.prefix{k:03d}, ScalarRandomizerBounds.emitted_append]\n')
            out.append('  apply List.mem_append_left _\n' if k>i+1 else '  exact List.mem_append_right _ member\n')
        length=min(16,252-16*i)
        previous=f'CompilerCompletion.emitted O.chunk{i-1:03d}' if i else '([] : List Row)'
        out.append(f'''def localRows{index} : List Row :=
  (List.range' {start+16*i} {length}).map booleanRow ++
    {previous} ++ CompilerCompletion.emitted O.chunk{index}
private theorem included{index} : ∀ row ∈ localRows{index}, row ∈ rows := by
  intro row member
  simp only [localRows{index}, List.mem_append] at member
  rcases member with (boolean | previous) | current
  · exact boolean_included _ (by decide) row boolean
''')
        out.append(f'  · exact product_included{i-1:03d} row previous\n' if i else '  · cases previous\n')
        out.append(f'''  · exact product_included{index} row current
theorem local_chain{index} : ScalarRows.checkChain R.p localRows{index} R.c{i}Initial R.c{i}Steps = true := by decide
theorem local_bits{index} : ScalarBits.checkBits R.p localRows{index} (R.c{i}Steps.map ScalarRows.StepData.left) = true := by decide
theorem chain{index} : ScalarRows.checkChain R.p rows R.c{i}Initial R.c{i}Steps = true :=
  ScalarChunkComposition.chain_check_lift R.p localRows{index} rows included{index} _ _ local_chain{index}
theorem bits{index} : ScalarBits.checkBits R.p rows (R.c{i}Steps.map ScalarRows.StepData.left) = true :=
  ScalarChunkComposition.bits_check_lift R.p localRows{index} rows included{index} _ local_bits{index}
''')
    names=[f'{i:03d}' for i in range(count)];global_checks='true'
    for i in reversed(range(count)):global_checks=f'(ScalarRows.checkChain R.p rows R.c{i}Initial R.c{i}Steps && {global_checks})'
    out.append('''theorem checked_chain : ScalarRows.checkChain R.p rows [(0,1)] R.steps = true := by
  apply ScalarChunkComposition.chunks_certificate R.p rows [(0,1)] R.chunks
  simp only [R.chunks, ScalarChunkComposition.checkChunks]
''')
    out.extend(f'  rw [R.c{i}endpoint]\n' for i in range(count-1))
    out.append(f'  change {global_checks} = true\n  simp only ['+', '.join('chain'+name for name in names)+', Bool.true_and]\n')
    out.append('''theorem checked_bits : ScalarBits.checkBits R.p rows (R.steps.map ScalarRows.StepData.left) = true := by
  have checked : ScalarChunkComposition.checkBitChunks R.p rows ['''+
               ', '.join(f'(R.c{i}Steps.map ScalarRows.StepData.left)' for i in range(count))+'''] = true := by
    simp only [ScalarChunkComposition.checkBitChunks, '''+', '.join('bits'+name for name in names)+''', Bool.true_and]
  simpa only [R.steps, R.chunks, List.flatten_cons, List.flatten_nil, List.map_append, List.map_nil,
    List.append_nil] using ScalarChunkComposition.bit_chunks_certificate R.p rows _ checked
''')
    out.append(f'''theorem bit_order : R.steps.map ScalarRows.StepData.left =
    (List.range' {start} 252).map (fun column => [(column,1)]) := by decide
theorem checked_reconstruction : ScalarComparisonBounds.checkEquality R.p rows
    (ScalarBits.bitLinear (R.steps.map ScalarRows.StepData.left)) [({value},1)] = true := by
  have localCheck := ScalarBitReconstruction.checked_reconstruction_indexed R.p
    [reconstructionRow {value} (List.range' {start} 252)] 0
    (R.steps.map ScalarRows.StepData.left) (List.range' {start} 252) [({value},1)] bit_order (by decide)
  apply ScalarChunkComposition.equality_check_lift R.p _ rows _ _ _ localCheck
  intro row member
  apply List.mem_append_left _
  apply List.mem_append_right _
  exact member
theorem kept_outside : ∀ column ∈ O.kept, column < {start} ∨ {start+252} ≤ column := by
  have checked : O.kept.all (fun column => decide (column < {start} ∨ {start+252} ≤ column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
def construct {{F : Type}} [Field F] (base : Nat → F) (n : Nat) : Nat → F :=
  ScalarRandomizerCompletion.construct base {start} n O.allStages
theorem constructs {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0) :
    Satisfies (construct base n) rows ∧
      binary (ScalarBits.decodeBits (construct base n) (R.steps.map ScalarRows.StepData.left)) = n ∧
      eval (construct base n) (ScalarComparisonBounds.endpoint [(0,1)] R.steps) = 1 ∧
      (∀ column ∈ O.kept, construct base n column = base column) :=
  ScalarRandomizerCompletion.constructs base {value} {start} n O.allStages O.kept R.steps
    canonical meaning one four O.ordered O.products (by decide) (by decide) kept_outside
    bit_order checked_bits checked_chain checked_reconstruction R.checked_maximum
''')
    out.extend('#print axioms '+name+'\n' for name in ('checked_chain','checked_bits','bit_order',
               'checked_reconstruction','kept_outside','constructs'))
    out.append(f'end ShielddSecurity.{ns}\n')
    source=''.join(out)
    blocks=_kept_blocks(plan,kept_block_size)
    if blocks is not None:
        original=f'''theorem kept_outside : ∀ column ∈ O.kept, column < {start} ∨ {start+252} ≤ column := by
  have checked : O.kept.all (fun column => decide (column < {start} ∨ {start+252} ≤ column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
'''
        bounded=_KEPT_APPEND_PROPERTY+''.join(f'''private theorem kept_outside_part{part:03d} :
    ∀ column ∈ O.keptPart{part:03d}, column < {start} ∨ {start+252} ≤ column := by
  have checked : O.keptPart{part:03d}.all
      (fun column => decide (column < {start} ∨ {start+252} ≤ column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
''' for part in range(len(blocks)))
        bounded+=f'''theorem kept_outside : ∀ column ∈ O.kept, column < {start} ∨ {start+252} ≤ column := by
  exact '''+_kept_property(blocks,start,start+252,'kept_outside_part','O.')+'\n'
        if source.count(original)!=1:
            raise relation.RelationError('exact protected-bit proof template required')
        source=source.replace(original,bounded,1)
    source=source.replace('O.','ShielddSecurity.'+order_namespace+'.').replace(
        'R.','ShielddSecurity.'+sound_namespace+'.')
    return _signature_audits(source)


def generate_randomizer_original_completion(data, accepted_roles, extracted):
    """Transport the constructed assignment to every captured comparator row.

    Original endpoint/copy assertions are derived after construction. They are
    never supplied as equality-stage legality or desired witness premises.
    """
    plan=fixed.randomizer_completion_plan(data,accepted_roles,extracted)
    checked,_,_,*_=fixed._selection(data,accepted_roles,extracted)
    return render_randomizer_original_completion(checked,plan)


def render_randomizer_original_completion(checked,plan,*,namespace='RuntimeFixedSpendRandomizerCompletion',
        order_namespace='RuntimeFixedSpendRandomizerOrder',sound_namespace='RuntimeTransferRandomizer',kept_block_size=None):
    """Neutral exact signed/outlining original-row transport after construction."""
    value,start=plan['value'],plan['bit_start'];copy=checked['metadata']['constant_copy']
    ns=namespace;R='ShielddSecurity.'+sound_namespace
    O='ShielddSecurity.'+order_namespace
    source=render_randomizer_completion(plan,namespace=namespace,order_namespace=order_namespace,
        sound_namespace=sound_namespace,kept_block_size=kept_block_size)
    source=source.removesuffix(f'end ShielddSecurity.{ns}\n')
    out=[source,f'''private theorem transport_row {{F : Type}} [Field F] [CharP F {R}.p]
    (rho : Nat → F) (linked : rho {copy} = rho 0) (actual expected : Row)
    (leftEqual : Compiler.canonical {R}.p (Compiler.unoutline {copy} actual.a) =
      Compiler.canonical {R}.p expected.a ∨
      Compiler.canonical {R}.p (Compiler.unoutline {copy} actual.a) =
        Compiler.canonical {R}.p (scaleLinear (-1) expected.a))
    (rightEqual : Compiler.canonical {R}.p (Compiler.unoutline {copy} actual.b) =
      Compiler.canonical {R}.p expected.b)
    (sound : Square (eval rho expected.a) (eval rho expected.b)) :
    Square (eval rho actual.a) (eval rho actual.b) := by
  rcases leftEqual with positive | negative
  · rw [← Compiler.canonical_equal rho _ _ positive,
      ← Compiler.canonical_equal rho _ _ rightEqual] at sound
    simpa only [Compiler.eval_unoutline rho {copy} _ linked] using sound
  · have negated : Square (eval rho (scaleLinear (-1) expected.a)) (eval rho expected.b) := by
      simpa [Square, eval_scale] using sound
    rw [← Compiler.canonical_equal rho _ _ negative,
      ← Compiler.canonical_equal rho _ _ rightEqual] at negated
    simpa only [Compiler.eval_unoutline rho {copy} _ linked] using negated
''']
    by_step={stage['step']:stage for stage in plan['stages']}
    for i in range(16):
        index=f'{i:03d}';end=min(252,16*i+16)
        expectations=[(f'booleanRow {start+j}',None,start+j) for j in range(16*i,end)]
        for j in range(max(1,16*i),end):
            stage=by_step[j];l,r,rem=(linear(stage[key]) for key in ('left','right','remainder'))
            output,aux=stage['output'],stage['auxiliary'];block=(j-1)//16
            if block not in (i-1,i):raise relation.RelationError('randomizer bounded product block coverage')
            expectations.extend(((f'⟨Compiler.subtract {l} {r},[({aux},1)]⟩',block,None),
                 (f'⟨{l} ++ {r},[({aux},1)] ++ scaleLinear 4 ([({output},1)] ++ {rem})⟩',block,None)))
        out.append(f'''theorem original_coverage{index} : ∀ actual ∈ {R}.c{i}Raw,
    ∃ expected ∈ localRows{index},
      (Compiler.canonical {R}.p (Compiler.unoutline {copy} actual.a) = Compiler.canonical {R}.p expected.a ∨
       Compiler.canonical {R}.p (Compiler.unoutline {copy} actual.a) = Compiler.canonical {R}.p (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical {R}.p (Compiler.unoutline {copy} actual.b) = Compiler.canonical {R}.p expected.b := by
  intro actual member
  simp only [{R}.c{i}Raw,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in expectations)+'\n')
        for expected,block,column in expectations:
            out.append(f'  · refine ⟨{expected}, ?_, by decide, by decide⟩\n')
            out.append(f'    simp only [localRows{index},List.mem_append]\n')
            if block is None:
                out.append(f'    exact Or.inl (Or.inl (List.mem_map.mpr ⟨{column}, by decide, rfl⟩))\n')
            else:
                out.append('    exact Or.inr (by decide)\n' if block==i else '    exact Or.inl (Or.inr (by decide))\n')
    out.append(f'''theorem actual_original_rows_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) : Satisfies (construct base n) {R}.originalRows := by
  have completed := constructs base n canonical meaning one four
  have copyLink : construct base n {copy} = construct base n 0 := by
    rw [completed.2.2.2 {copy} (by decide), completed.2.2.2 0 (by decide), linked]
  have oneValue : construct base n 0 = 1 := (completed.2.2.2 0 (by decide)).trans one
  have endpointValue := completed.2.2.1
  intro actual member
  obtain ⟨block, blockMember, present⟩ := List.mem_flatten.mp member
  simp only [{R}.originalBlocks,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at blockMember
  rcases blockMember with '''+' | '.join('rfl' for _ in range(17))+'\n')
    for i in range(16):
        index=f'{i:03d}'
        out.append(f'''  · obtain ⟨expected, inside, leftEqual, rightEqual⟩ := original_coverage{index} actual present
    exact transport_row (construct base n) copyLink actual expected leftEqual rightEqual
      (completed.1 expected (included{index} expected inside))
''')
    out.append(f'''  · simp only [{R}.tailRaw,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl
    · apply transport_row (construct base n) copyLink _ ⟨[],[]⟩ (by decide) (by decide)
      simp [Square,eval]
    · apply transport_row (construct base n) copyLink _
        (reconstructionRow {value} (List.range' {start} 252)) (by decide) (by decide)
      apply completed.1
      apply List.mem_append_left _
      apply List.mem_append_right _
      exact List.mem_singleton_self _
    · apply transport_row (construct base n) copyLink _
        ⟨Compiler.subtract (ScalarComparisonBounds.endpoint [(0,1)] {R}.steps) [(0,1)],[]⟩ (by decide) (by decide)
      simp [Square,Compiler.eval_subtract,eval,endpointValue,oneValue]
#print axioms actual_original_rows_complete
end ShielddSecurity.{ns}
''')
    source=''.join(out)
    blocks=_kept_blocks(plan,kept_block_size)
    if blocks is not None:
        for column in (copy,0):
            original=f'completed.2.2.2 {column} (by decide)'
            if source.count(original)!=(1 if column==copy else 2):
                raise relation.RelationError('exact protected original-row membership proof required')
            source=source.replace(original,f'completed.2.2.2 {column} '+_kept_membership(blocks,column,O+'.'))
    return _signature_audits(source)


def generate_randomizer_bit_completion(data, accepted_roles, extracted):
    """Derive source bit meanings from the same constructed canonical scalar."""
    plan=fixed.randomizer_completion_plan(data,accepted_roles,extracted);start=plan['bit_start']
    checked,*_=fixed._selection(data,accepted_roles,extracted)
    return render_randomizer_bit_completion(checked,plan)


def render_randomizer_bit_completion(checked,plan,*,namespace='RuntimeFixedSpendRandomizerCompletion',
        order_namespace='RuntimeFixedSpendRandomizerOrder',sound_namespace='RuntimeTransferRandomizer',kept_block_size=None):
    """Neutral singleton-bit reflection from the same constructed assignment."""
    start=plan['bit_start'];ns=namespace;O='ShielddSecurity.'+order_namespace
    source=render_randomizer_original_completion(checked,plan,namespace=namespace,
        order_namespace=order_namespace,sound_namespace=sound_namespace,kept_block_size=kept_block_size)
    source='import ShielddSecurity.CompilerSupportPreservation\n'+source.removesuffix(f'end ShielddSecurity.{ns}\n')
    source+=f'''theorem bit_reflection {{F : Type}} [Field F] (base : Nat → F) (n index : Nat)
    (bound : index < 252) :
    eval (construct base n) [({start}+index,1)] =
      (if (encodeBits 252 n)[index]?.getD false then 1 else 0) := by
  have selected : (List.range' {start} 252)[index]? = some ({start}+index) := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_range'] using bound)]
    simp only [List.getElem_range',Nat.one_mul]
  have columnMember := List.mem_of_getElem? selected
  have initialMember : booleanRow ({start}+index) ∈ {O}.initialRows := by
    apply List.mem_append_left _
    exact List.mem_map.mpr ⟨{start}+index,columnMember,rfl⟩
  have preserved := CompilerSupportPreservation.run_support
    (writeBits base {start} (encodeBits 252 n)) {O}.allStages {O}.kept {O}.initialRows {O}.ordered
    (booleanRow ({start}+index)) initialMember ({start}+index,1) (by simp [booleanRow])
  have columnValue : construct base n ({start}+index) = writeBits base {start} (encodeBits 252 n) ({start}+index) := preserved
  simp only [eval,Int.cast_one,one_mul,add_zero]
  rw [columnValue]
  have lower : {start} ≤ {start}+index := by omega
  have upper : {start}+index < {start}+(encodeBits 252 n).length := by
    rw [encodeBits_length]
    omega
  have position : {start}+index-{start} = index := by omega
  have inside : {start} ≤ {start}+index ∧ {start}+index < {start}+(encodeBits 252 n).length :=
    ⟨lower,upper⟩
  simp only [writeBits,if_pos inside,position]
#print axioms bit_reflection
end ShielddSecurity.{ns}
'''
    return _signature_audits(source)


def generate_window_curve_completion(data, accepted_roles, extracted, window_offset=1):
    """Discharge the actual nonfolded window's denominator and curve invariant.

    Boolean meanings and the incoming curve invariant are upstream semantics.
    Constructed selectors/products derive division legality and the outgoing
    invariant; no row satisfaction or desired point is an input.
    """
    plan=fixed.fixed_completion_plan(data,accepted_roles,extracted)
    checked,*_=fixed._selection(data,accepted_roles,extracted)
    return render_window_curve_completion(checked,plan,window_offset)


def render_window_curve_completion(checked,plan,window_offset=1,*,stem=None):
    """Neutral exact six-product/two-quotient curve construction renderer."""
    if type(window_offset)!=int or not 0<=window_offset<plan['window_count']:
        raise relation.RelationError('fixed curve completion offset')
    window=plan['windows'][window_offset];stages=window['stages'];index=window['index']
    if [stage['kind'] for stage in stages]!=['product']*6+['quotient']*2:
        raise relation.RelationError('fixed curve completion requires six exact products and two quotients')
    before,selected,_=checked['points'][window_offset];copy=checked['metadata']['constant_copy']
    stem=stem or f'RuntimeFixedSpendWindow{index:03d}'
    W='ShielddSecurity.'+stem
    C=W+'Completion';ns=stem+'CurveCompletion'
    out=[f'import {W}\nimport {C}\n',f'namespace ShielddSecurity.{ns}\n',
         'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
         f'''theorem prefix_ordered : GroupCircuitCompletion.Topological {C}.kept [] {C}.productStages :=
  GroupCircuitOrder.checked_order {C}.kept [] {C}.productStages (by decide)
theorem prefix_rows_complete {{F : Type}} [Field F] (rho : Nat → F) :
    Satisfies ({C}.productAssignment rho) (GroupCircuitCompletion.emitted {C}.productStages) :=
  GroupCircuitCompletion.run_constructs rho {C}.productStages {C}.kept prefix_ordered
    (by simp [{C}.productStages,GroupCircuitCompletion.Legal,GroupCircuitCompletion.Step.Legal,CompilerCompletion.Step.Legal])
theorem prefix_kept {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (member : column ∈ {C}.kept) : {C}.productAssignment rho column = rho column :=
  GroupCircuitCompletion.run_preserves rho {C}.productStages {C}.kept [] prefix_ordered column member
private theorem eval_kept {{F : Type}} [Field F] (base built : Nat → F) (terms : Linear)
    (preserves : ∀ column ∈ {C}.kept, built column = base column)
    (checked : terms.all (fun term => decide (term.1 ∈ {C}.kept)) = true) :
    eval built terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact preserves term.1 (of_decide_eq_true (List.all_eq_true.mp checked term member))
theorem prefix_eval_kept {{F : Type}} [Field F] (rho : Nat → F) (terms : Linear)
    (checked : terms.all (fun term => decide (term.1 ∈ {C}.kept)) = true) :
    eval ({C}.productAssignment rho) terms = eval rho terms :=
  eval_kept rho ({C}.productAssignment rho) terms (prefix_kept rho) checked
theorem prefix_input_preserved {{F : Type}} [Field F] (rho : Nat → F) :
    {W}.input ({C}.productAssignment rho) = {W}.input rho := by
  apply congrArg₂ Group.Point.mk
''']
    for lc in before:out.append(f'  · exact prefix_eval_kept rho {linear(lc)} (by decide)\n')
    for i,stage in enumerate(stages[:6]):
        out.append(f'''private theorem prefix_product{i} {{F : Type}} [Field F] [CharP F {W}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    eval ({C}.productAssignment rho) {W}.p{i}_output =
      eval ({C}.productAssignment rho) {W}.p{i}_left * eval ({C}.productAssignment rho) {W}.p{i}_right := by
  have oneBuilt : {C}.productAssignment rho 0 = 1 := (prefix_kept rho 0 (by decide)).trans one
  have product := ScalarRows.checked_product_sound ({C}.productAssignment rho) oneBuilt
    ({W}.fourNonzero (F := F)) (GroupCircuitCompletion.emitted {C}.productStages) (prefix_rows_complete rho)
    {W}.p{i}_left {W}.p{i}_right {W}.p{i}_output (.product [({stage['auxiliary']},1)]) (by decide)
  simpa only [mul_comm] using product
''')
    out.append(f'''theorem constructed_selector {{F : Type}} [Field F] [CharP F {W}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    {W}.selected ({C}.productAssignment rho) =
      Group.windowPoint (eval ({C}.productAssignment rho) {W}.low)
        (eval ({C}.productAssignment rho) {W}.high) {W}.base {W}.twice {W}.triple := by
  let built := {C}.productAssignment rho
  have oneBuilt : built 0 = 1 := (prefix_kept rho 0 (by decide)).trans one
  apply congrArg₂ Group.Point.mk
''')
    for axis in range(2):
        out.append(f'''  · have left := Compiler.canonical_equal built {W}.p{axis}_left {W}.high (by decide)
    have right := Compiler.canonical_equal built {W}.p{axis}_right (Compiler.subtract {W}.hi{axis} {W}.lo{axis}) (by decide)
    have result := Compiler.canonical_equal built {W}.p{axis}_output
      (Compiler.subtract {linear(selected[axis])} {W}.lo{axis}) (by decide)
    simp only [Compiler.eval_subtract] at right result
    have product := prefix_product{axis} rho one
    rw [left,right,result] at product
    calc
      _ = eval built {W}.lo{axis} + eval built {W}.high * (eval built {W}.hi{axis} - eval built {W}.lo{axis}) :=
        (sub_eq_iff_eq_add.mp product).trans (add_comm _ _)
      _ = _ := by
        simp only [{W}.selected,Group.windowPoint,Group.chooseCoordinate,{W}.base,{W}.twice,{W}.triple,
          {W}.lo{axis},{W}.hi{axis},eval_append,eval_scale,eval,oneBuilt,Int.cast_one,Int.cast_zero,
          Int.cast_sub,mul_one,zero_mul,add_zero,zero_add]
        ring
''')
    out.append(f'''theorem constructed_denominators {{F : Type}} [Field F] [CharP F {W}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) :
    eval ({C}.productAssignment rho) {C}.denominator0 = 1 + Group.delta ({W}.coefficientD : F)
      ({W}.input rho) ({W}.selected ({C}.productAssignment rho)) ∧
    eval ({C}.productAssignment rho) {C}.denominator1 = 1 - Group.delta ({W}.coefficientD : F)
      ({W}.input rho) ({W}.selected ({C}.productAssignment rho)) := by
  let built := {C}.productAssignment rho
  have oneBuilt : built 0 = 1 := (prefix_kept rho 0 (by decide)).trans one
  have xx := prefix_product2 rho one
  have yy := prefix_product3 rho one
  have xy := prefix_product5 rho one
  simp only [{W}.p2_left,{W}.p2_right,{W}.p2_output] at xx
  simp only [{W}.p3_left,{W}.p3_right,{W}.p3_output] at yy
  simp only [{W}.p5_left,{W}.p5_right,{W}.p5_output] at xy
  change eval built {W}.xx = ({W}.input built).x * ({W}.selected built).x at xx
  change eval built {W}.yy = ({W}.input built).y * ({W}.selected built).y at yy
  change eval built {W}.xyProduct = eval built {W}.xx * eval built {W}.yy at xy
  rw [xx,yy] at xy
  constructor
''')
    for axis,sign in ((0,1),(1,-1)):
        out.append(f'''  · have checked := Compiler.canonical_equal built {C}.denominator{axis}
      ([(0,1)] ++ scaleLinear {'('+W+'.coefficientD)' if sign==1 else '(-'+W+'.coefficientD)'} {W}.xyProduct) (by decide)
    simp only [eval_append,eval_scale,eval,oneBuilt,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at checked
    rw [checked,xy]
    rw [← prefix_input_preserved rho]
    unfold Group.delta
    ring
''')
    parameters=f'''    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({W}.coefficientD : F)) (imaginarySquare : imaginary * imaginary = -1)
    (low high : Bool) (lowValue : eval rho {W}.low = if low then 1 else 0)
    (highValue : eval rho {W}.high = if high then 1 else 0)
    (inputValid : Group.OnCurve ({W}.coefficientD : F) ({W}.input rho))
    (linked : rho {copy} = rho 0)'''
    out.append(f'''theorem actual_curve_rows_complete {{F : Type}} [Field F] [CharP F {W}.modulus]
{parameters} :
    Satisfies ({C}.completeAssignment rho) {C}.rawRows ∧
      (∀ column ∈ {C}.kept, {C}.completeAssignment rho column = rho column) := by
  have selectedValid : Group.OnCurve ({W}.coefficientD : F) ({W}.selected ({C}.productAssignment rho)) := by
    rw [constructed_selector rho one, prefix_eval_kept rho {W}.low (by decide),
      prefix_eval_kept rho {W}.high (by decide), lowValue, highValue]
    exact Group.window_onCurve ({W}.coefficientD : F) low high {W}.base {W}.twice {W}.triple
      ({W}.base_onCurve rho one) ({W}.twice_onCurve rho one) ({W}.triple_onCurve rho one)
  have nonzero := Group.denominators_nonzero ({W}.coefficientD : F) imaginary nonSquare imaginarySquare
    ({W}.input rho) ({W}.selected ({C}.productAssignment rho)) inputValid selectedValid
  have formulas := constructed_denominators rho one
  exact {C}.local_rows_complete rho linked
    (by rw [formulas.1]; exact nonzero.1) (by rw [formulas.2]; exact nonzero.2)
''')
    audits=('prefix_ordered','prefix_rows_complete','prefix_kept','prefix_eval_kept','prefix_input_preserved',
            'constructed_selector','constructed_denominators','actual_curve_rows_complete')
    out.extend('#print axioms '+name+'\n' for name in audits)
    out.append(f'end ShielddSecurity.{ns}\n')
    return _signature_audits(''.join(out))


def generate_window_complete(data, accepted_roles, extracted, window_offset=0):
    """Construct every actual window row and derive the outgoing curve invariant."""
    plan=fixed.fixed_completion_plan(data,accepted_roles,extracted)
    checked,*_=fixed._selection(data,accepted_roles,extracted)
    return render_window_complete(checked,plan,window_offset)


def render_window_complete(checked,plan,window_offset=0,*,stem=None):
    """Neutral local construction, including the folded initial window."""
    if type(window_offset)!=int or not 0<=window_offset<plan['window_count']:
        raise relation.RelationError('fixed complete window offset')
    window=plan['windows'][window_offset];index=window['index'];stages=window['stages']
    stem=stem or f'RuntimeFixedSpendWindow{index:03d}'
    W='ShielddSecurity.'+stem;C=W+'Completion'
    ns=stem+'CurveCompletion';copy=checked['metadata']['constant_copy']
    before,_,_=checked['points'][window_offset]
    folded=index==0 and all(stage['kind'] in ('product','linear') for stage in stages)
    if folded:
        source=f'''import {W}
import {C}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
private theorem eval_kept {{F : Type}} [Field F] (base built : Nat → F) (terms : Linear)
    (preserves : ∀ column ∈ {C}.kept, built column = base column)
    (checked : terms.all (fun term => decide (term.1 ∈ {C}.kept)) = true) :
    eval built terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact preserves term.1 (of_decide_eq_true (List.all_eq_true.mp checked term member))
theorem local_rows_constructed {{F : Type}} [Field F] [CharP F {W}.modulus]
    (rho : Nat → F) (linked : rho {copy} = rho 0) :
    Satisfies ({C}.completeAssignment rho) {C}.rawRows ∧
      (∀ column ∈ {C}.kept, {C}.completeAssignment rho column = rho column) :=
  {C}.local_rows_complete rho linked
#print axioms local_rows_constructed
'''
        completion='local_rows_constructed rho linked'
    else:
        source=render_window_curve_completion(checked,plan,window_offset,stem=stem)
        source=source.removesuffix(f'end ShielddSecurity.{ns}\n')
        completion='actual_curve_rows_complete rho one imaginary nonSquare imaginarySquare low high lowValue highValue inputValid linked'
    out=[source,f'''theorem actual_window_complete {{F : Type}} [Field F] [CharP F {W}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ({W}.coefficientD : F)) (imaginarySquare : imaginary * imaginary = -1)
    (low high : Bool) (lowValue : eval rho {W}.low = if low then 1 else 0)
    (highValue : eval rho {W}.high = if high then 1 else 0)
    (inputValid : Group.OnCurve ({W}.coefficientD : F) ({W}.input rho))
    (linked : rho {copy} = rho 0) :
    Satisfies ({C}.completeAssignment rho) {W}.rawRows ∧
      Group.OnCurve ({W}.coefficientD : F) ({W}.output ({C}.completeAssignment rho)) ∧
      (∀ column ∈ {C}.kept, {C}.completeAssignment rho column = rho column) := by
  have completed := {completion}
  let built := {C}.completeAssignment rho
  have oneBuilt : built 0 = 1 := (completed.2 0 (by decide)).trans one
  have lowBuilt : eval built {W}.low = if low then 1 else 0 :=
    (eval_kept rho built {W}.low completed.2 (by decide)).trans lowValue
  have highBuilt : eval built {W}.high = if high then 1 else 0 :=
    (eval_kept rho built {W}.high completed.2 (by decide)).trans highValue
  have inputSame : {W}.input built = {W}.input rho := by
    apply congrArg₂ Group.Point.mk
''']
    for lc in before:out.append(f'    · exact eval_kept rho built {linear(lc)} completed.2 (by decide)\n')
    out.append(f'''  have coverage : {W}.rawRows.all (fun row => decide
      (row ∈ {C}.rawRows ∨ row = ⟨{W}.low,{W}.low⟩ ∨ row = ⟨{W}.high,{W}.high⟩)) = true := by decide
  have allRows : Satisfies built {W}.rawRows := by
    intro row member
    have casesRow := of_decide_eq_true (List.all_eq_true.mp coverage row member)
    rcases casesRow with inside | rfl | rfl
    · exact completed.1 row inside
    · change Square (eval built {W}.low) (eval built {W}.low)
      rw [lowBuilt]
      cases low <;> simp [Square]
    · change Square (eval built {W}.high) (eval built {W}.high)
      rw [highBuilt]
      cases high <;> simp [Square]
  have arithmetic := {W}.actual_arithmetic built oneBuilt allRows
  have selectedValid : Group.OnCurve ({W}.coefficientD : F) ({W}.selected built) := by
    rw [arithmetic.2,lowBuilt,highBuilt]
    exact Group.window_onCurve ({W}.coefficientD : F) low high {W}.base {W}.twice {W}.triple
      ({W}.base_onCurve rho one) ({W}.twice_onCurve rho one) ({W}.triple_onCurve rho one)
  have incomingValid : Group.OnCurve ({W}.coefficientD : F) ({W}.input built) := by
    rw [inputSame]
    exact inputValid
  have xRow : ({W}.output built).x *
      (1 + Group.delta ({W}.coefficientD : F) ({W}.input built) ({W}.selected built)) =
        Group.cross ({W}.input built) ({W}.selected built) :=
    arithmetic.1.1.trans (by unfold Group.cross; ring)
  have outputValid := Group.affine_rows_onCurve ({W}.coefficientD : F) imaginary nonSquare imaginarySquare
    ({W}.input built) ({W}.selected built) ({W}.output built) incomingValid selectedValid
    xRow arithmetic.1.2
  exact ⟨allRows,outputValid,completed.2⟩
#print axioms actual_window_complete
end ShielddSecurity.{ns}
''')
    return _signature_audits(''.join(out))


def generate_window_program(data, accepted_roles, extracted, window_offset=0):
    """Adapt a proved actual window to symbolic construction/support rules.

    The bounded initial packet validates canonical support and both allocation
    cursors. Later whole-loop generation must use the all126 bounds join.
    """
    bounds=fixed.fixed_completion_bounds(data,accepted_roles,extracted)
    plan=fixed.fixed_completion_plan(data,accepted_roles,extracted)
    checked,*_=fixed._selection(data,accepted_roles,extracted)
    if type(window_offset)!=int or not 0<=window_offset<len(bounds['frames']):
        raise relation.RelationError('fixed program window offset')
    return _window_program_source(checked,bounds['frames'][window_offset],bounds,plan['kept'],window_offset)


def generate_window_programs(captures, accepted_roles, extractions):
    """Exact all126 adapters; refuse incomplete captures or support cursors."""
    bounds=fixed.fixed_completion_bounds_join(captures,accepted_roles,extractions)
    selections=[fixed._selection(data,accepted_roles,extracted)[0]
                for data,extracted in zip(captures,extractions)]
    kept=fixed.fixed_completion_plan(captures[0],accepted_roles,extractions[0])['kept']
    result={}
    for checked in selections:
        start=checked['metadata']['window_start']
        for offset in range(checked['metadata']['window_count']):
            frame=bounds['frames'][start+offset]
            result[f'RuntimeFixedSpendWindow{frame["index"]:03d}Program']=_window_program_source(
                checked,frame,bounds,kept,offset)
    if len(result)!=126:raise relation.RelationError('fixed program adapter coverage')
    return result


def _window_program_source(checked, frame, bounds, kept, window_offset,*,stem=None):
    index=frame['index']
    before,_,after=checked['points'][window_offset]
    stem=stem or f'RuntimeFixedSpendWindow{index:03d}'
    W='ShielddSecurity.'+stem
    C=W+'Completion';V=W+'CurveCompletion'
    ns=stem+'Program'
    copy=bounds['constant_copy'];high_start=bounds['high_start']
    source=f'''import {V}
import ShielddSecurity.GroupFixedCircuitBounds
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
def kept : List Nat := {kept}
def before : GroupFixedCircuitBounds.Frame := ⟨{frame['before']['low']},{frame['before']['high']}⟩
def after : GroupFixedCircuitBounds.Frame := ⟨{frame['after']['low']},{frame['after']['high']}⟩
def program (low high : Bool) : GroupFixedCircuitCompletion.Program where
  stages := {C}.completionSteps
  rows := {W}.rawRows
  input := ({linear(before[0])},{linear(before[1])})
  output := ({linear(after[0])},{linear(after[1])})
  low := {W}.low
  high := {W}.high
  lowBit := low
  highBit := high

theorem local_constructor {{F : Type}} [Field F] [CharP F {W}.modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({W}.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1) (low high : Bool) :
    GroupFixedCircuitCompletion.LocalConstruct ({W}.coefficientD : F) {copy} (program low high) := by
  intro rho one linked incoming lowValue highValue
  have completed := {V}.actual_window_complete rho one imaginary nonSquare imaginarySquare
    low high lowValue highValue incoming linked
  exact ⟨completed.1,completed.2.1⟩
#print axioms local_constructor

theorem caller_protected (low high : Bool) :
    GroupFixedCircuitCompletion.Protected kept (program low high) := by
  have checked : {C}.completionSteps.all
      (fun stage => GroupCircuitOrder.checkOutside kept stage.writes) = true := by decide
  intro stage member column present written
  exact (of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)) present
#print axioms caller_protected

theorem checked_bounds (low high : Bool) :
    (before.low ≤ after.low ∧ before.high ≤ after.high) ∧
      GroupFixedCircuitBounds.RowsCovered {high_start} {copy} after (program low high).rows ∧
      GroupFixedCircuitBounds.WritesOutside {high_start} {copy} before (program low high) :=
  GroupFixedCircuitBounds.checked_local {high_start} {copy} before after (program low high) (by
    change GroupFixedCircuitBounds.checkLocal {high_start} {copy} before after (program false false) = true
    decide)
#print axioms checked_bounds
end ShielddSecurity.{ns}
'''
    return _signature_audits(source)


def generate_full_completion(captures, accepted_roles, extractions):
    """Construct all126 actual windows and invoke the existing native join.

    Full capture/source/ordinary row joins and support certificates are strict
    prerequisites. Every local constructor proof is supplied internally.
    """
    ownership=fixed.fixed_completion_join(captures,accepted_roles,extractions)
    bounds=fixed.fixed_completion_bounds_join(captures,accepted_roles,extractions)
    randomizer=fixed.randomizer_completion_plan(captures[0],accepted_roles,extractions[0])
    checked=[fixed._selection(data,accepted_roles,extracted)[0]
             for data,extracted in zip(captures,extractions)]
    return render_full_completion(ownership,bounds,randomizer,checked)


def render_full_completion(ownership,bounds,randomizer,checked,*,window_stems=None,chunk_stems=None,
        namespace='RuntimeTransferFixedSpendCompletion',sound_namespace='RuntimeTransferFixedSpend',
        canonical_namespace='RuntimeTransferRandomizer',order_namespace='RuntimeFixedSpendRandomizerOrder',
        scalar_completion_namespace='RuntimeFixedSpendRandomizerCompletion'):
    """Neutral actual126 local construction and exact native endpoint renderer."""
    W=['ShielddSecurity.'+name for name in window_stems] if window_stems is not None else [f'ShielddSecurity.RuntimeFixedSpendWindow{i:03d}' for i in range(126)]
    P=[name+'Program' for name in W]
    chunks=['ShielddSecurity.'+name for name in chunk_stems] if chunk_stems is not None else [f'ShielddSecurity.RuntimeFixedSpendChunk{item["metadata"]["window_start"]:03d}' for item in checked]
    A='ShielddSecurity.'+sound_namespace
    R='ShielddSecurity.'+scalar_completion_namespace
    O='ShielddSecurity.'+order_namespace
    B='ShielddSecurity.'+canonical_namespace
    start=randomizer['bit_start'];copy=bounds['constant_copy'];high_start=bounds['high_start']
    kept=ownership['kept'];external=sorted(set(kept)-set(range(start,start+252)))
    for item in checked:
        for offset in range(item['metadata']['window_count']):
            index=item['metadata']['window_start']+offset
            bits=item['metadata']['bits'][2*index:2*index+2]
            for axis,bit in enumerate(bits):
                if item['observed'][source_index(bit)]!=((start+2*index+axis,1),):
                    raise relation.RelationError('fixed constructor bit support is not exact canonical singleton')
    bit=lambda i:f'(encodeBits 252 n)[{i}]?.getD false'
    program=lambda i:f'({P[i]}.program ({bit(2*i)}) ({bit(2*i+1)}))'
    out=[f'import {A}\nimport {R}\n',
         ''.join(f'import {name}\n' for name in P),
         '''namespace ShielddSecurity.RuntimeTransferFixedSpendCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
''',
         f'def kept : List Nat := {kept}\ndef external : List Nat := {external}\n',
         'def programs (n : Nat) : List GroupFixedCircuitCompletion.Program := ['+
         ','.join(program(i) for i in range(126))+']\n',
         'def segments (n : Nat) : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) := ['+
         ','.join(f'({program(i)},{P[i]}.after)' for i in range(126))+']\n',
         f'def construct {{F : Type}} [Field F] (base : Nat → F) (n : Nat) : Nat → F :=\n'
         f'  GroupFixedCircuitCompletion.run ({R}.construct base n) (programs n)\n',
         f'''theorem certified_bounds (n : Nat) :
    GroupFixedCircuitBounds.Certified {high_start} {copy} {P[0]}.before (segments n) := by
  unfold segments
''']
    for i in range(126):
        out.append(f'  have bounds{i:03d} := {P[i]}.checked_bounds ({bit(2*i)}) ({bit(2*i+1)})\n')
        out.append(f'  refine ⟨bounds{i:03d}.1,bounds{i:03d}.2.1,bounds{i:03d}.2.2,?_⟩\n')
    out.append('  trivial\n#print axioms certified_bounds\n')
    out.append('''private theorem emitted_member (programs : List GroupFixedCircuitCompletion.Program)
    (program : GroupFixedCircuitCompletion.Program) (member : program ∈ programs)
    (row : Row) (present : row ∈ program.rows) : row ∈ GroupFixedCircuitCompletion.rows programs := by
  induction programs with
  | nil => simp at member
  | cons first tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst program
        exact List.mem_append_left _ present
      · exact List.mem_append_right _ (ih later)
''')
    out.append(f'''theorem actual_rows_complete {{F : Type}} [Field F] [CharP F {A}.modulus]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {randomizer['value']} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1) (linked : base {copy} = base 0) :
    Satisfies (construct base n) {A}.rawRows ∧
      Group.OnCurve ({A}.coefficientD : F) ({A}.contribution (construct base n)) ∧
      (∀ column ∈ external, construct base n column = base column) := by
  let rho := {R}.construct base n
  have randomizer := {R}.constructs base n canonical meaning one four
  have initial := {R}.actual_original_rows_complete base n canonical meaning one four linked
  have rhoOne : rho 0 = 1 := (randomizer.2.2.2 0 (by decide)).trans one
  have rhoLink : rho {copy} = rho 0 := by
    rw [randomizer.2.2.2 {copy} (by decide),randomizer.2.2.2 0 (by decide),linked]
  have localConstructors : ∀ program ∈ programs n,
      GroupFixedCircuitCompletion.LocalConstruct ({A}.coefficientD : F) {copy} program := by
    intro program member
    simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in range(126))}
''')
    for i in range(126):
        out.append(f'    · exact {P[i]}.local_constructor imaginary nonSquare imaginarySquare ({bit(2*i)}) ({bit(2*i+1)})\n')
    out.append('''  have protection : ∀ program ∈ programs n, GroupFixedCircuitCompletion.Protected kept program := by
    intro program member
    simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with '''+' | '.join('rfl' for _ in range(126))+'\n')
    for i in range(126):out.append(f'    · exact {P[i]}.caller_protected ({bit(2*i)}) ({bit(2*i+1)})\n')
    out.append('''  have supports : ∀ program ∈ programs n, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept := by
    have checked : (programs n).all (fun program => (program.low ++ program.high).all
      (fun term => decide (term.1 ∈ kept))) = true := by
      change (programs 0).all (fun program => (program.low ++ program.high).all
        (fun term => decide (term.1 ∈ kept))) = true
      decide
    intro program member term present
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp checked program member) term present)
''')
    out.append(f'''  have initialCovered : GroupFixedCircuitBounds.RowsCovered {high_start} {copy}
      {P[0]}.before {B}.originalRows := by
    have checked : {B}.originalRows.all (fun row => (row.a ++ row.b).all
        (fun term => decide (GroupFixedCircuitBounds.covers {high_start} {copy} {P[0]}.before term.1))) = true := by decide
    intro row member term present
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
  have fresh : GroupFixedCircuitCompletion.Fresh {B}.originalRows (programs n) := by
    have result := GroupFixedCircuitBounds.bounded_fresh {high_start} {copy} {P[0]}.before
      {B}.originalRows (segments n) initialCovered (certified_bounds n)
    simpa only [segments,programs,List.map_cons,List.map_nil,Prod.fst] using result
  have alignment : GroupFixedCircuitCompletion.Aligned ([],[(0,1)]) (programs n) := by
    simp only [programs,GroupFixedCircuitCompletion.Aligned,{','.join(name+'.program' for name in P)},and_self]
  have incoming : Group.OnCurve ({A}.coefficientD : F)
      (GroupFixedCircuitCompletion.point rho ([],[(0,1)])) := by
    simp [GroupFixedCircuitCompletion.point,Group.OnCurve,eval,rhoOne]
  have bitMeanings : ∀ program ∈ programs n,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0) := by
    intro program member
    simp only [programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in range(126))}
''')
    for i in range(126):
        out.append(f'    · exact ⟨{R}.bit_reflection base n {2*i} (by decide),\n'
                   f'        {R}.bit_reflection base n {2*i+1} (by decide)⟩\n')
    out.append(f'''  have completed := GroupFixedCircuitCompletion.constructs ({A}.coefficientD : F) {copy}
    rho (programs n) ([],[(0,1)]) {B}.originalRows kept localConstructors protection supports fresh
    alignment (by decide) (by decide) rhoOne rhoLink initial incoming bitMeanings
  have allRows : Satisfies (construct base n) {A}.rawRows := by
    intro row member
    obtain ⟨block,blockMember,present⟩ := List.mem_flatten.mp member
    simp only [{A}.blocks,List.mem_cons,List.not_mem_nil,or_false] at blockMember
    rcases blockMember with {' | '.join('rfl' for _ in range(len(chunks)+1))}
''')
    for item,chunk in zip(checked,chunks):
        indices=range(item['metadata']['window_start'],item['metadata']['window_start']+item['metadata']['window_count'])
        out.append(f'    · obtain ⟨window,windowMember,present⟩ := List.mem_flatten.mp present\n'
                   f'      simp only [{chunk}.blocks,List.mem_cons,List.not_mem_nil,or_false] at windowMember\n'
                   f'      rcases windowMember with {" | ".join("rfl" for _ in indices)}\n')
        for i in indices:
            out.append(f'      · have selected : (programs n)[{i}]? = some {program(i)} := rfl\n'
                       f'        exact completed.1 row (List.mem_append_right _\n'
                       f'          (emitted_member (programs n) {program(i)} (List.mem_of_getElem? selected) row present))\n')
    out.append('''    · exact completed.1 row (List.mem_append_left _ present)
  have callerSelection : external.all (fun column => decide (column ∈ kept ∧ column ∈ '''+O+'''.kept)) = true := by decide
  refine ⟨allRows,?_,?_⟩
  · simpa only [programs,GroupFixedCircuitCompletion.output,'''+','.join(name+'.program' for name in P)+f''',
      {A}.contribution,GroupFixedCircuitCompletion.point,{chunks[-1]}.output,{W[-1]}.output] using completed.2.1
  · intro column member
    have selected := of_decide_eq_true (List.all_eq_true.mp callerSelection column member)
    exact (completed.2.2 column selected.1).trans (randomizer.2.2.2 column selected.2)
#print axioms actual_rows_complete
theorem actual_native_bytes_complete {{F J : Type}} [Field F] [CharP F {A}.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {randomizer['value']} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (two : (2 : F) ≠ 0) (codec : TransferReduction.CanonicalField F)
    (writer : GroupByteCodec.BEWrite codec) (model : Group.StandardCurveModel J ({A}.coefficientD : F))
    (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F)) (imaginarySquare : imaginary * imaginary = -1)
    (spendAuth : J) (spendAuthRole : ({A}.generator : Group.Point F) = model.coordinates spendAuth)
    (linked : base {copy} = base 0) :
    codec.decode (eval (construct base n) {B}.privateValue) < Scalar.order ∧
      {A}.contribution (construct base n) = GroupNativeMultiply.nativeMultiply ({A}.coefficientD : F)
        {A}.generator (GroupByteCodec.reader (writer.encode (eval (construct base n) {B}.privateValue))) := by
  have completed := actual_rows_complete base n canonical meaning one four imaginary nonSquare imaginarySquare linked
  have preserved := completed.2.2 0 (by decide)
  exact {A}.actual_fixed_native_bytes (construct base n) (preserved.trans one) four imaginary two codec writer model
    nonSquare imaginarySquare spendAuth spendAuthRole completed.1
#print axioms actual_native_bytes_complete
end ShielddSecurity.RuntimeTransferFixedSpendCompletion
''')
    return _signature_audits(''.join(out).replace('RuntimeTransferFixedSpendCompletion',namespace))


def generate_window(data, accepted_roles, extracted, window_offset=0):
    checked,raw,normalized,products,quotients,_=fixed._selection(data,accepted_roles,extracted)
    return render_window(checked,raw,normalized,products,quotients,window_offset)


def render_window(checked,raw,normalized,products,quotients,window_offset=0,*,stem=None):
    """Render only separately accepted source LCs and actual row certificates."""
    obj=checked['metadata'];size=obj['window_count']
    if type(window_offset) is not int or not 0<=window_offset<size:
        raise relation.RelationError('fixed candidate window offset')
    index=obj['window_start']+window_offset;ns=stem or f'RuntimeFixedSpendWindow{index:03d}'
    qns=ns+'Div';Q='ShielddSecurity.'+qns;copy=obj['constant_copy']
    roles=[f'window.{index}.select.0',f'window.{index}.select.1',
           *[f'window.{index}.{name}' for name in ('xx','yy','sum','xy')]]
    used={i for role in roles for i in products[role]['rows']}
    copy_index=next(i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),()))
    used.add(copy_index)
    bits=[checked['observed'][source_index(bit)] for bit in obj['bits'][2*index:2*index+2]]
    for bit in bits:
        used.add(next(i for i,row in normalized.items() if row==(bit,bit)))
    certificates=[];qused={copy_index}
    for axis in range(2):
        role=f'window.{index}.quotient.{axis}';c=dict(quotients[role],role=role)
        certificates.append(c);qused.update(c['rows'])
    qsource=generate_quotient_boundaries(dict(outline=copy,rows={i:raw[i] for i in sorted(qused)},
                                            certificates=certificates),checked['metadata_sha256'],
                                          obj['relation_digest'],namespace=qns)
    out=['import ShielddSecurity.GroupFixedWindows\nimport ShielddSecurity.GroupRowCompletion\nimport ShielddSecurity.CompilerCompletion\nimport ShielddSecurity.ScalarBits\n',
         qsource.removeprefix('import ShielddSecurity.Compiler\n'),
         f'\nnamespace ShielddSecurity.{ns}\nset_option maxHeartbeats 500000\n',
         f'-- Diagnostic metadata SHA256: {checked["metadata_sha256"]}; original relation: {obj["relation_digest"]}\n',
         f'def modulus : Nat := {relation.MODULUS}\ndef coefficientD : Int := {signed(fixed.D)}\n',
         f'def originalRows : List Nat := {sorted(used|qused)}\n',
         'def localRows : List Row := [\n'+',\n'.join('⟨'+linear(raw[i][0])+', '+linear(raw[i][1])+'⟩' for i in sorted(used))+']\n',
         f'def rawRows : List Row := localRows ++ {Q}.rawRows\ndef rows : List Row := Compiler.unoutlineRows {copy} rawRows\n',
         f'theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n',
         '''theorem fourNonzero {F : Type} [Field F] [CharP F modulus] : (4 : F) ≠ 0 := by
  intro zero
  have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
    (by decide) (by decide) (by simpa using zero)
  omega
''']
    completion_source,completion_names=_completion_sources(certificates,raw,normalized,copy)
    out.append(completion_source)
    captures={role:(left,right,result) for role,left,right,result in checked['products']}
    for number,role in enumerate(roles):
        left,right,result=captures[role];cert=products[role]
        product_completion,product_names=_product_completion_sources(
            f'p{number}',left,right,result,cert,raw,normalized,copy)
        out.append(product_completion);completion_names+=product_names
        for name,lc in zip(('left','right','output'),(left,right,result)):
            out.append(f'def p{number}_{name} : Linear := {linear(lc)}\n')
        swapped=cert.get('swapped',False);a,b=(f'p{number}_right',f'p{number}_left') if swapped else (f'p{number}_left',f'p{number}_right')
        if cert['kind']=='product':datum='.product '+linear(cert['auxiliary'])
        elif cert['kind']=='square':datum='.square'
        else:datum=('.foldedLeft ' if cert['kind']=='folded_left' else '.foldedRight ')+'('+str(signed(cert['coefficient']))+' : Int)'
        out.append(f'''theorem p{number}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho p{number}_output = eval rho p{number}_left * eval rho p{number}_right := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product := ScalarRows.checked_product_sound rho one (fourNonzero (F := F)) rows normalized
    {a} {b} p{number}_output ({datum}) (by decide)
  simpa only [mul_comm] using product
''')
    before,selected,after=checked['points'][window_offset]
    for role,point in zip(('input','selected','output'),(before,selected,after)):
        out.append(f'def {role} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(point[0])},eval rho {linear(point[1])}⟩\n')
    table=checked['tables'][window_offset];table_names=('base','twice','triple','nextBase')
    for role,point in zip(table_names,table):
        out.append(f'def {role} {{F : Type}} [Field F] : Group.Point F := ⟨(({signed(point[0])} : Int) : F),(({signed(point[1])} : Int) : F)⟩\n')
    for role,lc in zip(('low','high'),bits):out.append(f'def {role} : Linear := {linear(lc)}\n')
    for axis in range(2):
        b,t,u=(signed(point[axis]) for point in table[:3]);identity=axis
        out.append(f'def lo{axis} : Linear := [(0,{identity})] ++ scaleLinear ({b} - ({identity})) low\n')
        out.append(f'def hi{axis} : Linear := [(0,{t})] ++ scaleLinear ({u} - ({t})) low\n')
    arithmetic_lcs=[]
    window=obj['windows'][window_offset]
    def lc(ref):return checked['observed'][source_index(ref['source'])] if 'source' in ref else canonical([(0,int(ref['native'],16))])
    for name,ref in zip(('xx','yy','sumProduct','xyProduct'),window['arithmetic']):
        arithmetic_lcs.append(lc(ref));out.append(f'def {name} : Linear := {linear(lc(ref))}\n')
    for name,ref in zip(('nx','ny','dx','dy'),window['quotient'][:4]):out.append(f'def {name} : Linear := {linear(lc(ref))}\n')
    out.append('''theorem actual_arithmetic {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    TransferOwnership.AddEquations (coefficientD : F) (input rho) (selected rho) (output rho) ∧
    selected rho = Group.windowPoint (eval rho low) (eval rho high) base twice triple := by
''')
    for number in range(6):
        out.append(f'  have p{number} := p{number}_sound rho one satisfied\n')
        out.append(f'  simp only [p{number}_left,p{number}_right,p{number}_output] at p{number}\n')
    out.append('''  change eval rho xx = (input rho).x * (selected rho).x at p2
  change eval rho yy = (input rho).y * (selected rho).y at p3
  change eval rho xyProduct = eval rho xx * eval rho yy at p5
''')
    for side,point,role in (('left',before,'input'),('right',selected,'selected')):
        out.append(f'''  have sum{side} := Compiler.canonical_equal rho p4_{side}
    ({linear(point[0])} ++ {linear(point[1])}) (by decide)
  simp only [eval_append] at sum{side}
  change eval rho p4_{side} = ({role} rho).x + ({role} rho).y at sum{side}
''')
    out.append('''  have p4Value := p4_sound rho one satisfied
  rw [sumleft,sumright] at p4Value
  change eval rho sumProduct = ((input rho).x+(input rho).y) *
    ((selected rho).x+(selected rho).y) at p4Value
''')
    desired={
        'nx':'(sumProduct ++ scaleLinear (-1) xx) ++ scaleLinear (-1) yy',
        'ny':'yy ++ xx',
        'dx':'[(0,1)] ++ scaleLinear coefficientD xyProduct',
        'dy':'[(0,1)] ++ scaleLinear (-coefficientD) xyProduct'}
    for name,expression in desired.items():
        target={'nx':'eval rho sumProduct - eval rho xx - eval rho yy',
                'ny':'eval rho yy + eval rho xx','dx':'1 + (coefficientD : F) * eval rho xyProduct',
                'dy':'1 - (coefficientD : F) * eval rho xyProduct'}[name]
        out.append(f'''  have {name}Value : eval rho {name} = {target} := by
    have checked := Compiler.canonical_equal rho {name} ({expression}) (by decide)
    simpa only [eval_append,eval_scale,eval,one,Int.cast_one,Int.cast_neg,one_mul,add_zero,
      sub_eq_add_neg,neg_one_mul,neg_mul] using checked
''')
    out.append(f'''  have qs : Satisfies rho {Q}.rawRows := by
    intro row member
    exact satisfied row (List.mem_append.mpr (Or.inr member))
  have qx := {Q}.equation0_sound rho one (fourNonzero (F := F)) qs
  have qy := {Q}.equation1_sound rho one (fourNonzero (F := F)) qs
  change (output rho).x * eval rho dx = eval rho nx at qx
  change (output rho).y * eval rho dy = eval rho ny at qy
  rw [nxValue,dxValue,p5,p4Value,p3,p2] at qx
  rw [nyValue,dyValue,p5,p3,p2] at qy
  constructor
  · constructor
    · simp only [TransferOwnership.AddEquations,Group.delta,Group.cross] at qx ⊢
      convert qx using 1 <;> ring
    · simp only [TransferOwnership.AddEquations,Group.delta,Group.diagonal] at qy ⊢
      convert qy using 1 <;> ring
  · apply congrArg₂ Group.Point.mk
''')
    for axis in range(2):
        out.append(f'''    · have left := Compiler.canonical_equal rho p{axis}_left high (by decide)
      have right := Compiler.canonical_equal rho p{axis}_right (Compiler.subtract hi{axis} lo{axis}) (by decide)
      have result := Compiler.canonical_equal rho p{axis}_output
        (Compiler.subtract {linear(selected[axis])} lo{axis}) (by decide)
      simp only [Compiler.eval_subtract] at right result
      have product := p{axis}_sound rho one satisfied
      rw [left,right,result] at product
      calc
        _ = eval rho lo{axis} + eval rho high * (eval rho hi{axis} - eval rho lo{axis}) :=
          (sub_eq_iff_eq_add.mp product).trans (add_comm _ _)
        _ = _ := by
          simp only [selected,Group.windowPoint,Group.chooseCoordinate,base,twice,triple,
            lo{axis},hi{axis},eval_append,eval_scale,eval,one,Int.cast_one,Int.cast_zero,
            Int.cast_sub,mul_one,zero_mul,add_zero,zero_add]
          ring
''')
    # Native table correctness is checked from integer polynomial identities,
    # then lifted through complete-curve addition. No table weight is assumed.
    simp_defs=','.join(table_names)+',coefficientD,Group.delta,Group.cross,Group.diagonal,Group.OnCurve'
    for role,(x,y) in zip(table_names,table):
        x,y=signed(x),signed(y)
        out.append(f'''theorem {role}_onCurve {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) : Group.OnCurve (coefficientD : F) ({role} : Group.Point F) := by
  have checked := Compiler.canonical_equal rho
    [(0,({y}:Int)*({y}:Int)-({x}:Int)*({x}:Int))]
    [(0,1+coefficientD*({x}:Int)*({x}:Int)*({y}:Int)*({y}:Int))] (by decide)
  simp only [eval,one,mul_one,add_zero,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_one] at checked
  simpa only [{simp_defs}] using checked
''')
    for number,(a,b,c) in enumerate((('base','base','twice'),('twice','base','triple'),('twice','twice','nextBase'))):
        ax,ay=map(signed,table[table_names.index(a)]);bx,by=map(signed,table[table_names.index(b)]);cx,cy=map(signed,table[table_names.index(c)])
        out.append(f'''theorem table{number} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1) :
    ({c} : Group.Point F) = GroupFixedWindows.nativeAdd (coefficientD : F) {a} {b} := by
  have xrow : ({c} : Group.Point F).x * (1+Group.delta (coefficientD : F) {a} {b}) = Group.cross {a} {b} := by
    have checked := Compiler.canonical_equal rho
      [(0,({cx}:Int)*(1+coefficientD*({ax}:Int)*({bx}:Int)*({ay}:Int)*({by}:Int)))]
      [(0,({ax}:Int)*({by}:Int)+({ay}:Int)*({bx}:Int))] (by decide)
    simp only [eval,one,mul_one,add_zero,Int.cast_mul,Int.cast_add,Int.cast_one] at checked
    simpa only [{simp_defs}] using checked
  have yrow : ({c} : Group.Point F).y * (1-Group.delta (coefficientD : F) {a} {b}) = Group.diagonal {a} {b} := by
    have checked := Compiler.canonical_equal rho
      [(0,({cy}:Int)*(1-coefficientD*({ax}:Int)*({bx}:Int)*({ay}:Int)*({by}:Int)))]
      [(0,({ay}:Int)*({by}:Int)+({ax}:Int)*({bx}:Int))] (by decide)
    simp only [eval,one,mul_one,add_zero,Int.cast_mul,Int.cast_sub,Int.cast_add,Int.cast_one] at checked
    simpa only [{simp_defs}] using checked
  have left := {a}_onCurve rho one
  have right := {b}_onCurve rho one
  exact (Group.affine_rows_sound (coefficientD : F) imaginary nonSquare imaginarySquare
    {a} {b} {c} left right xrow yrow).trans
      (GroupFixedWindows.native_add_affine (coefficientD : F) imaginary nonSquare imaginarySquare
        {a} {b} left right).symm
''')
    out.append('''noncomputable def window {F : Type} [Field F] (rho : Nat → F) : GroupFixedWindows.FixedWindowWitness F :=
  ⟨ScalarBits.decodeBit rho low,ScalarBits.decodeBit rho high,twice,triple,nextBase,output rho⟩
theorem fixed_equations {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (satisfied : Satisfies rho rawRows) :
    GroupFixedWindows.FixedWindowEquations (coefficientD : F) (input rho) base (window rho) := by
  have arithmetic := actual_arithmetic rho one satisfied
''')
    out.append(f'''  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have lowValue := ScalarBits.checked_bit_value rho rows normalized [low,high] (by decide) low (by simp)
  have highValue := ScalarBits.checked_bit_value rho rows normalized [low,high] (by decide) high (by simp)
  refine ⟨⟨table0 rho one imaginary nonSquare imaginarySquare,
    table1 rho one imaginary nonSquare imaginarySquare,table2 rho one imaginary nonSquare imaginarySquare⟩, ?_⟩
  have addition := arithmetic.1
  rw [arithmetic.2,lowValue,highValue] at addition
  simpa only [window] using addition
theorem actual_window_coordinates {{F J : Type}} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (acc weightedBase : J) (inputRole : input rho = model.coordinates acc)
    (baseRole : (base : Group.Point F) = model.coordinates weightedBase)
    (satisfied : Satisfies rho rawRows) :
    output rho = model.coordinates (acc + GroupFixedWindows.fixedDigit (window rho) • weightedBase) ∧
    (nextBase : Group.Point F) = model.coordinates (4 • weightedBase) := by
  have equations := fixed_equations rho one imaginary nonSquare imaginarySquare satisfied
  rw [inputRole,baseRole] at equations
  exact GroupFixedWindows.fixed_window_coordinates (coefficientD : F) imaginary model nonSquare
    imaginarySquare acc weightedBase (window rho) equations
''')
    names=['constantLink','fourNonzero',*[f'p{i}_sound' for i in range(6)],'actual_arithmetic',
           *[role+'_onCurve' for role in table_names],*[f'table{i}' for i in range(3)],
           'fixed_equations','actual_window_coordinates']
    names += completion_names
    out.extend('#print axioms '+name+'\n' for name in names)
    out.append('end ShielddSecurity.'+ns+'\n')
    return _signature_audits(''.join(out))


def generate_canonical(data, accepted_roles, extracted):
    return fixed.generate_canonical(data,accepted_roles,extracted)


def generate_chunk(data, accepted_roles, extracted):
    """Compose at most16 checked windows in ascending captured order."""
    checked,*_=fixed._selection(data,accepted_roles,extracted)
    return render_chunk(checked)


def render_chunk(checked,*,namespace=None,window_stems=None):
    """Neutral bounded ascending fixed-window trace renderer."""
    obj=checked['metadata'];start,size=obj['window_start'],obj['window_count']
    names=['ShielddSecurity.'+name for name in window_stems] if window_stems is not None else [f'ShielddSecurity.RuntimeFixedSpendWindow{i:03d}' for i in range(start,start+size)]
    ns=namespace or f'RuntimeFixedSpendChunk{start:03d}'
    out=['import ShielddSecurity.GroupFixedChunks\n'+''.join('import '+name+'\n' for name in names),
         f'namespace ShielddSecurity.{ns}\nset_option maxHeartbeats 500000\n',
         'def blocks : List (List Row) := ['+','.join(name+'.rawRows' for name in names)+']\n',
         'def rawRows : List Row := blocks.flatten\n',
         f'def coefficientD : Int := {names[0]}.coefficientD\n',
         f'def modulus : Nat := {relation.MODULUS}\n',
         f'def input {{F : Type}} [Field F] (rho : Nat → F) := {names[0]}.input rho\n',
         f'def base {{F : Type}} [Field F] : Group.Point F := {names[0]}.base\n',
         f'def output {{F : Type}} [Field F] (rho : Nat → F) := {names[-1]}.output rho\n',
         f'def nextBase {{F : Type}} [Field F] : Group.Point F := {names[-1]}.nextBase\n',
         'noncomputable def windows {F : Type} [Field F] (rho : Nat → F) : List (GroupFixedWindows.FixedWindowWitness F) := ['+
         ','.join(name+'.window rho' for name in names)+']\n',
         '''theorem actual_trace {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (satisfied : Satisfies rho rawRows) :
    GroupFixedWindows.FixedTraceEquations (coefficientD : F) (input rho) base (windows rho) := by
''']
    for offset,name in enumerate(names):
        out.append(f'''  have sat{offset} : Satisfies rho {name}.rawRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨{name}.rawRows, by simp [blocks],member⟩)
  have equations{offset} := {name}.fixed_equations rho one imaginary nonSquare imaginarySquare sat{offset}
''')
    out.append('  unfold windows\n')
    for offset in range(size):
        out.append(f'  refine ⟨equations{offset}, ?_⟩\n')
    out.append('  exact True.intro\n')
    out.append('''theorem trace_output {F : Type} [Field F] (rho : Nat → F) :
    GroupFixedWindows.fixedTraceOutput (input rho) (windows rho) = output rho := rfl
theorem trace_base_assignment {F : Type} [Field F] (rho : Nat → F) :
    GroupFixedChunks.fixedTraceBase (base : Group.Point F) (windows rho) = nextBase := rfl
''')
    # Deliberately use one reusable symbolic trace theorem. No126-window walk.
    definitions='windows,input,base,output,GroupFixedWindows.fixedTraceOutput,'+','.join(name+'.window' for name in names)
    out.append(f'''theorem actual_chunk_coordinates {{F J : Type}} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (acc weightedBase : J) (inputRole : input rho = model.coordinates acc)
    (baseRole : (base : Group.Point F) = model.coordinates weightedBase)
    (satisfied : Satisfies rho rawRows) :
    output rho = model.coordinates
      (acc + TransferWindows.digitsValue ((windows rho).map GroupFixedWindows.fixedDigit) • weightedBase) := by
  have equations := actual_trace rho one imaginary nonSquare imaginarySquare satisfied
  rw [inputRole,baseRole] at equations
  have coordinates := GroupFixedWindows.fixed_trace_value_coordinates (coefficientD : F) imaginary
    model nonSquare imaginarySquare (windows rho) acc weightedBase equations
  simpa only [{definitions}] using coordinates
#print axioms actual_trace
#print axioms trace_output
#print axioms trace_base_assignment
#print axioms actual_chunk_coordinates
end ShielddSecurity.{ns}
''')
    return _signature_audits(''.join(out))


def generate_full(captures, accepted_roles, extractions):
    """Compose exact all126 observed windows and canonical bits on one rho.

    The native generator's standard group interpretation remains an explicit
    parameter/source contract; no scalar result or subgroup fact is assumed.
    """
    if (not isinstance(captures,list) or not isinstance(extractions,list)
            or len(captures)!=len(extractions) or not 1<=len(captures)<=8):
        raise relation.RelationError('fixed full candidate requires at most8 matching chunks')
    checked=[fixed._selection(data,accepted_roles,extracted)[0]
             for data,extracted in zip(captures,extractions)]
    fixed.join_chunks(checked)
    if extractions[0]['include_canonical'] is not True:
        raise relation.RelationError('fixed full candidate requires first chunk canonical rows')
    return render_full(checked)


def render_full(checked,*,namespace='RuntimeTransferFixedSpend',canonical_namespace='RuntimeTransferRandomizer',
        chunk_stems=None,window_stems=None):
    """Neutral actual complete fixed trace; typed acceptance belongs to ingress."""
    chunks=['ShielddSecurity.'+name for name in chunk_stems] if chunk_stems is not None else [f'ShielddSecurity.RuntimeFixedSpendChunk{item["metadata"]["window_start"]:03d}' for item in checked]
    windows=['ShielddSecurity.'+name for name in window_stems] if window_stems is not None else [f'ShielddSecurity.RuntimeFixedSpendWindow{i:03d}' for i in range(126)]
    R='ShielddSecurity.'+canonical_namespace
    out=['import ShielddSecurity.GroupByteCodec\nimport ShielddSecurity.RuntimeTransferRandomizer\n',
         ''.join('import '+name+'\n' for name in chunks),
         'namespace ShielddSecurity.RuntimeTransferFixedSpend\nset_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
         '''-- Native/source boundary at shieldd.lock844389ee069e1fb2e576708842d0b389b4d9a44a:
-- group.rs SHA256ca75207acfd6bcb794f9f54b8ab3f52b236478f6b10761d459747dcbb9155971.
-- Point<Scalar>::multiply161-167 reads Scalar::encode's32BEbytes at31-i/8,
-- i%8, i=0..254. commonware Scalar::as_slice641-650 uses
-- blst_scalar_from_fr + blst_bendian_from_scalar; Write745-749 copies those
-- bytes, FixedSize780-782 is32. Its arithmetic/FFI canonical BEwrite contract
-- must identify byte[j] with GroupScalarCodec.bigEndianByte(codec.decode value) j.
-- commonware source SHA256dafee3e8845a86e9862770681ff60ceefa201c1557695e15578738dad63bd720.
-- group.rs native_point103-115 reverses the SDK's32LE coordinate bytes and
-- Scalar::read_cfg AllowZero decodes BE; that source contract identifies each
-- native coordinate with the same canonical prime-field representative.
-- SDK lib.rs22-28 coordinates reads affine u/v.to_bytes (LE), source SHA256
-- 5bd0e5e4687f7053f82757758a552fc8dd8330aa0bacc56159597d8f8c9b0a11.
-- group.rs generator118-120 selects SDK SPEND_AUTH. The named spendAuth
-- parameter below denotes the standard Jubjub SpendAuth base obtained from
-- VerificationKey(SigningKey<SpendAuth>(canonical scalarone)); primitives
-- generators.rs SHA256b16f348693412a19eada6da78550575babcf11f563036b49e16dbcc91a8470fc.
-- The standard model/codec/source interpretation contracts are explicit:
-- no hash, witness value, desired scalar result or subgroup fact discharges them.
''',
         f'def modulus : Nat := {chunks[0]}.modulus\ndef coefficientD : Int := {chunks[0]}.coefficientD\n',
         'def blocks : List (List Row) := ['+','.join(name+'.rawRows' for name in chunks)+f',{R}.originalRows]\n',
         'def rawRows : List Row := blocks.flatten\n',
         f'def input {{F : Type}} [Field F] (rho : Nat → F) := {chunks[0]}.input rho\n',
         f'def generator {{F : Type}} [Field F] : Group.Point F := {chunks[0]}.base\n',
         f'def contribution {{F : Type}} [Field F] (rho : Nat → F) := {chunks[-1]}.output rho\n',
         'noncomputable def chunks {F : Type} [Field F] (rho : Nat → F) : List (List (GroupFixedWindows.FixedWindowWitness F)) := ['+
         ','.join(name+'.windows rho' for name in chunks)+']\n',
         'noncomputable def windows {F : Type} [Field F] (rho : Nat → F) := (chunks rho).flatten\n',
         f'noncomputable def decodedBits {{F : Type}} [Field F] (rho : Nat → F) := {R}.decodedBits rho\n',
         '''theorem input_identity {F : Type} [Field F] (rho : Nat → F) (one : rho 0 = 1) :
    input rho = Group.identityPoint := by
  apply congrArg₂ Group.Point.mk
  · rfl
  · exact (by simpa only [eval,Int.cast_one,mul_one,add_zero] using one)
theorem bits_role {F : Type} [Field F] (rho : Nat → F) :
    GroupFixedChunks.windowBits (windows rho) = decodedBits rho := rfl
theorem bits_width {F : Type} [Field F] (rho : Nat → F) :
    (decodedBits rho).length = 252 := rfl
theorem actual_trace {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (satisfied : Satisfies rho rawRows) :
    GroupFixedWindows.FixedTraceEquations (coefficientD : F) (input rho) generator (windows rho) := by
  apply GroupFixedChunks.chunks_trace
  unfold chunks
''']
    for i,name in enumerate(chunks):
        out.append(f'''  have sat{i} : Satisfies rho {name}.rawRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨{name}.rawRows,by simp [blocks],member⟩)
  have trace{i} := {name}.actual_trace rho one imaginary nonSquare imaginarySquare sat{i}
''')
    for i,name in enumerate(chunks):
        out.append(f'  refine ⟨trace{i}, ?_⟩\n')
        if i+1<len(chunks):out.append(f'  rw [{name}.trace_output,{name}.trace_base_assignment]\n')
    out.append('  exact True.intro\n')
    out.append('''theorem trace_output {F : Type} [Field F] (rho : Nat → F) :
    GroupFixedWindows.fixedTraceOutput (input rho) (windows rho) = contribution rho := rfl
theorem actual_fixed_scalar {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (standardGenerator : J) (generatorRole : (generator : Group.Point F) = model.coordinates standardGenerator)
    (satisfied : Satisfies rho rawRows) :
    contribution rho = model.coordinates (binary (decodedBits rho) • standardGenerator) := by
  have equations := actual_trace rho one imaginary nonSquare imaginarySquare satisfied
  have identityRole : input rho = model.coordinates (0 : J) :=
    (input_identity rho one).trans model.identity.symm
  rw [identityRole,generatorRole] at equations
  have order := (GroupFixedChunks.window_bits_digits (windows rho)).symm
  rw [bits_role rho] at order
  have result := GroupFixedWindows.fixed_trace_scalar_coordinates (coefficientD : F) imaginary model
    nonSquare imaginarySquare standardGenerator (windows rho) (decodedBits rho) order equations
  rw [← identityRole] at result
  exact (trace_output rho).symm.trans result
theorem actual_fixed_canonical {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (standardGenerator : J) (generatorRole : (generator : Group.Point F) = model.coordinates standardGenerator)
    (satisfied : Satisfies rho rawRows) :
    binary (decodedBits rho) < Scalar.order ∧
      (binary (decodedBits rho) : F) = eval rho RuntimeTransferRandomizer.privateValue ∧
      contribution rho = model.coordinates (binary (decodedBits rho) • standardGenerator) := by
  have randomizerSat : Satisfies rho RuntimeTransferRandomizer.originalRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨RuntimeTransferRandomizer.originalRows,by simp [blocks],member⟩)
  have scalar := RuntimeTransferRandomizer.actual_randomizer_bits rho one four randomizerSat
  exact ⟨scalar.1,scalar.2,actual_fixed_scalar rho one imaginary model nonSquare imaginarySquare
    standardGenerator generatorRole satisfied⟩
theorem actual_fixed_native {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (imaginary : F) (two : (2 : F) ≠ 0)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (standardGenerator : J) (generatorRole : (generator : Group.Point F) = model.coordinates standardGenerator)
    (satisfied : Satisfies rho rawRows) :
    contribution rho = GroupNativeMultiply.nativeMultiply (coefficientD : F) generator (decodedBits rho) := by
  rw [generatorRole,GroupNativeMultiply.native_multiply_coordinates (coefficientD : F) imaginary model
    nonSquare imaginarySquare two standardGenerator (decodedBits rho)]
  exact actual_fixed_scalar rho one imaginary model nonSquare imaginarySquare standardGenerator generatorRole satisfied
theorem actual_fixed_encoded_native {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F) (two : (2 : F) ≠ 0)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (standardGenerator : J) (generatorRole : (generator : Group.Point F) = model.coordinates standardGenerator)
    (satisfied : Satisfies rho rawRows) :
    contribution rho = GroupNativeMultiply.nativeMultiply (coefficientD : F) generator
      (GroupScalarCodec.encodedBits (binary (decodedBits rho))) := by
  have canonical := actual_fixed_canonical rho one four imaginary model nonSquare imaginarySquare
    standardGenerator generatorRole satisfied
  rw [GroupScalarCodec.encoded_reader,generatorRole,
    GroupScalarCodec.native_canonical_coordinates (coefficientD : F) imaginary model nonSquare imaginarySquare
      two standardGenerator (decodedBits rho) (bits_width rho) (binary (decodedBits rho)) canonical.1 rfl]
  rw [← generatorRole]
  exact actual_fixed_native rho one imaginary two model nonSquare imaginarySquare standardGenerator generatorRole satisfied
theorem actual_fixed_native_codec {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F) (two : (2 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (spendAuth : J) (spendAuthRole : (generator : Group.Point F) = model.coordinates spendAuth)
    (satisfied : Satisfies rho rawRows) :
    codec.decode (eval rho RuntimeTransferRandomizer.privateValue) < Scalar.order ∧
      contribution rho = GroupNativeMultiply.nativeMultiply (coefficientD : F) generator
        (GroupScalarCodec.encodedBits (codec.decode (eval rho RuntimeTransferRandomizer.privateValue))) := by
  have canonical := actual_fixed_canonical rho one four imaginary model nonSquare imaginarySquare
    spendAuth spendAuthRole satisfied
  have decoded : codec.decode (eval rho RuntimeTransferRandomizer.privateValue) = binary (decodedBits rho) := by
    rw [← canonical.2.1]
    exact TransferReduction.decode_canonical_cast codec _
      (lt_trans canonical.1 (by decide : Scalar.order < Scalar.modulus))
  rw [decoded]
  exact ⟨canonical.1,actual_fixed_encoded_native rho one four imaginary two model nonSquare
    imaginarySquare spendAuth spendAuthRole satisfied⟩
theorem actual_fixed_native_bytes {F J : Type} [Field F] [CharP F modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F) (two : (2 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (model : Group.StandardCurveModel J (coefficientD : F))
    (nonSquare : Group.NoUnitSquare (coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (spendAuth : J) (spendAuthRole : (generator : Group.Point F) = model.coordinates spendAuth)
    (satisfied : Satisfies rho rawRows) :
    codec.decode (eval rho RuntimeTransferRandomizer.privateValue) < Scalar.order ∧
      contribution rho = GroupNativeMultiply.nativeMultiply (coefficientD : F) generator
        (GroupByteCodec.reader (writer.encode (eval rho RuntimeTransferRandomizer.privateValue))) := by
  rw [GroupByteCodec.reader_join]
  exact actual_fixed_native_codec rho one four imaginary two codec model nonSquare imaginarySquare
    spendAuth spendAuthRole satisfied
theorem actual_randomizer_byte_bits {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F) (writer : GroupByteCodec.BEWrite codec)
    (satisfied : Satisfies rho rawRows) :
    GroupByteCodec.reader (writer.encode (eval rho RuntimeTransferRandomizer.privateValue)) =
      decodedBits rho ++ [false,false,false] := by
  have randomizerSat : Satisfies rho RuntimeTransferRandomizer.originalRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨RuntimeTransferRandomizer.originalRows,by simp [blocks],member⟩)
  have canonical := RuntimeTransferRandomizer.actual_randomizer_bits rho one four randomizerSat
  exact GroupByteCodec.canonical_reader_join codec writer (decodedBits rho) (bits_width rho)
    (eval rho RuntimeTransferRandomizer.privateValue) canonical.1 canonical.2
''')
    exports=['input_identity','bits_role','bits_width','actual_trace','trace_output','actual_fixed_scalar',
             'actual_fixed_canonical','actual_fixed_native','actual_fixed_encoded_native','actual_fixed_native_codec',
             'actual_fixed_native_bytes','actual_randomizer_byte_bits']
    out.extend('#print axioms '+name+'\n' for name in exports)
    out.append('end ShielddSecurity.RuntimeTransferFixedSpend\n')
    return _signature_audits(''.join(out).replace('RuntimeTransferRandomizer',canonical_namespace).replace('RuntimeTransferFixedSpend',namespace))
