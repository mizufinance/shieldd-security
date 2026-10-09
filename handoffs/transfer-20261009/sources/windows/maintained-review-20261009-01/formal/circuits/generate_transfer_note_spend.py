"""Construct the actual selected two-spend rows from independent branch inputs.

This requires source/row certificates, discovers six owned columns, and checks
every row's coverage in Lean. It never assigns note/hash/root/NF/shared roles.
"""
from . import transfer_note_spend as notes, transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index
from .generate_hash_round import linear, _signature_audits


def completion_plan(data, extracted, accepted_roles):
    selection=notes.certificates(data,extracted,accepted_roles)
    checked=selection['checked'];obj=checked['metadata'];certs=selection['certificates']
    optional=obj['spends'][1]['optional']
    unprotected={source_index(v['source']) for v in [optional['selected'],
                 *(p[2] for p in optional['products'])]}
    protected={0,1,2,obj['constant_copy']}
    for lc in accepted_roles['observed'].values():protected.update(c for c,_ in lc)
    for handle,lc in checked['observed'].items():
        if handle not in unprotected:protected.update(c for c,_ in lc)
    products=[]
    for name in ('selector','anchor','amount'):
        cert=certs['product.'+name]
        auxiliary=cert.get('auxiliary')
        if (cert['kind']!='product' or not isinstance(auxiliary,tuple) or len(auxiliary)!=1
                or auxiliary[0][1]!=1 or auxiliary[0][0] in protected):
            raise relation.RelationError('note-spend completion needs a fresh unit auxiliary: '+name)
        pivots=[c for c,v in cert['output'] if v==1 and c not in protected]
        if len(pivots)!=1:
            raise relation.RelationError('note-spend completion product pivot absent/ambiguous: '+name)
        product=pivots[0];aux=auxiliary[0][0]
        remainder=tuple((c,v) for c,v in cert['output'] if c!=product)
        products.append(dict(name=name,product=product,auxiliary=aux,remainder=remainder,
                             swapped=cert['swapped'],rows=cert['rows']))
    writes=[c for product in products for c in (product['product'],product['auxiliary'])]
    if len(set(writes))!=6 or set(writes)&protected:
        raise relation.RelationError('note-spend completion owned columns alias shared roles')
    for p in products:
        cert=certs['product.'+p['name']]
        if any(c in writes for c,_ in cert['left']+cert['right']+p['remainder']):
            raise relation.RelationError('note-spend completion fused/input support touches writes')
        protected.update(c for c,_ in p['remainder'])
    return dict(selection=selection,products=products,writes=writes,kept=sorted(protected))


def generate_completion(data,extracted,accepted_roles):
    plan=completion_plan(data,extracted,accepted_roles)
    selection=plan['selection'];checked=selection['checked'];obj=checked['metadata'];copy=obj['constant_copy']
    certs=selection['certificates'];raw=selection['rows'];products=plan['products']
    out=['''import ShielddSecurity.RuntimeTransferNoteSpend
import ShielddSecurity.NoteSpendRowCompletion
import ShielddSecurity.CompilerOrder
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferNoteSpendCompletion
open RuntimeTransferNoteSpend
-- All thirteen current branch rows only. Hash/tree/range/native construction
-- remains a prior-stage obligation; every captured source boundary is kept.
''',f'-- Relation: {obj["relation_digest"]}; metadata SHA256: {checked["metadata_sha256"]}\n',
         f'def kept : List Nat := {plan["kept"]}\ndef completionWrites : List Nat := {plan["writes"]}\n',
         '''def inputs : NoteSpendCompletion.Inputs :=
  ⟨dummy,synthetic,optionalRealNullifier,optionalNullifier,optionalComputedAnchor,optionalAnchor,optionalAmount⟩
''']
    pairs=[('dummy','Compiler.subtract synthetic optionalRealNullifier'),
           ('Compiler.subtract [(0,1)] dummy','Compiler.subtract optionalComputedAnchor optionalAnchor'),
           ('dummy','optionalAmount')]
    targets=['Compiler.subtract optionalNullifier optionalRealNullifier','[]','[]']
    for i,p in enumerate(products):
        left,right=pairs[i]
        if p['swapped']:left,right=right,left
        out.append(f'def left{i} : Linear := {left}\ndef right{i} : Linear := {right}\n')
        out.append(f'def remainder{i} : Linear := {linear(p["remainder"])}\n')
        out.append(f'def output{i} : Linear := [({p["product"]},1)] ++ remainder{i}\ndef target{i} : Linear := {targets[i]}\n')
    out.append('def stage0 {F : Type} [Field F] (rho : Nat → F) : Nat → F :=\n  '+
               f'ScalarCompletion.extendProduct rho left0 right0 remainder0 {products[0]["product"]} {products[0]["auxiliary"]}\n')
    out.append('def stage1 {F : Type} [Field F] (rho : Nat → F) : Nat → F :=\n  '+
               f'ScalarCompletion.extendProduct (stage0 rho) left1 right1 remainder1 {products[1]["product"]} {products[1]["auxiliary"]}\n')
    out.append('def completeAssignment {F : Type} [Field F] (rho : Nat → F) : Nat → F :=\n  '+
               f'ScalarCompletion.extendProduct (stage1 rho) left2 right2 remainder2 {products[2]["product"]} {products[2]["auxiliary"]}\n')
    asserts=[('required.nullifier','requiredRealNullifier','requiredNullifier'),
             ('required.anchor','requiredComputedAnchor','requiredAnchor')]
    steps=[f'.product left{i} right{i} remainder{i} {p["product"]} {p["auxiliary"]}' for i,p in enumerate(products)]
    req=[];expected={}
    for role,left,right in asserts:
        if certs[role]['reverse']:left,right=right,left
        req.append((left,right));steps.append(f'.equal {left} {right}')
        expected[certs[role]['row']]=f'⟨Compiler.subtract {left} {right},[]⟩'
    steps.append('.squareEqual dummy dummy');expected[certs['optional.boolean']['row']]='⟨dummy,dummy⟩'
    assertion_pairs=[]
    for i,name in enumerate(('selected','anchor','amount')):
        left,right=f'output{i}',f'target{i}'
        if certs['optional.'+name]['reverse']:left,right=right,left
        assertion_pairs.append((left,right));steps.append(f'.equal {left} {right}')
        expected[certs['optional.'+name]['row']]=f'⟨Compiler.subtract {left} {right},[]⟩'
        p=products[i]
        expected[p['rows'][0]]=f'⟨Compiler.subtract left{i} right{i},[({p["auxiliary"]},1)]⟩'
        expected[p['rows'][1]]=f'⟨left{i} ++ right{i},[({p["auxiliary"]},1)] ++ scaleLinear 4 output{i}⟩'
    steps.append('.equal [] []')
    copy_row=next(i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),()))
    expected[copy_row]='⟨[],[]⟩'
    if set(expected)!=set(raw):raise relation.RelationError('note-spend completion physical row coverage mismatch')
    out.append('def completionSteps : List CompilerCompletion.Step := [\n  '+',\n  '.join(steps)+']\n')
    out.append('''theorem completion_ordered_checked : CompilerOrder.checkOrder kept [] completionSteps = true := by decide
theorem completion_ordered : CompilerCompletion.Topological kept [] completionSteps :=
  CompilerOrder.checked_order kept [] completionSteps completion_ordered_checked
theorem completion_run {F : Type} [Field F] (rho : Nat → F) :
    CompilerCompletion.run rho completionSteps = completeAssignment rho := by rfl

theorem kept_preserved {F : Type} [Field F] (rho : Nat → F) (column : Nat)
    (member : column ∈ kept) : completeAssignment rho column = rho column := by
  rw [← completion_run]
  exact CompilerCompletion.run_preserves rho completionSteps kept [] completion_ordered column member

theorem source_preserved {F : Type} [Field F] (rho : Nat → F) (terms : Linear)
    (certificate : terms.all (fun term => decide (term.1 ∈ kept)) = true) :
    eval (completeAssignment rho) terms = eval rho terms := by
  apply eval_agrees
  intro term member
  exact kept_preserved rho term.1 (of_decide_eq_true ((List.all_eq_true.mp certificate) term member))
''')
    def preserve(stage,terms):
        p=products[stage];base=('rho','stage0 rho','stage1 rho')[stage]
        return f'NoteSpendRowCompletion.product_eval_preserves ({base}) left{stage} right{stage} remainder{stage} {terms} {p["product"]} {p["auxiliary"]} (by decide)'
    for i,p in enumerate(products):
        base=('rho','stage0 rho','stage1 rho')[i]
        out.append(f'''theorem materialized{i} {{F : Type}} [Field F] (rho : Nat → F) :
    eval (completeAssignment rho) output{i} = eval rho left{i} * eval rho right{i} := by
''')
        if i<2:
            out.append('  simp only [completeAssignment]\n')
            out.append(f'  rw [{preserve(2,"output"+str(i))}]\n')
        if i==0:out.append(f'  simp only [stage1]\n  rw [{preserve(1,"output0")}]\n')
        out.append(f'  have value := NoteSpendRowCompletion.materialized_value ({base}) left{i} right{i} remainder{i} {p["product"]} {p["auxiliary"]} (by decide)\n')
        if i:
            for side in ('left','right'):
                if i==1:
                    out.append(f'  have {side}Agree : eval (stage0 rho) {side}{i} = eval rho {side}{i} := {preserve(0,side+str(i))}\n')
                else:
                    out.append(f'''  have {side}Agree : eval (stage1 rho) {side}{i} = eval rho {side}{i} :=
    ({preserve(1,side+str(i))}).trans ({preserve(0,side+str(i))})
''')
            out.append('  rw [leftAgree,rightAgree] at value\n')
        out.append('  exact value\n')
    out.append('''theorem completion_coverage : ∀ actual ∈ RuntimeTransferNoteSpend.rawRows,
    ∃ expected ∈ CompilerCompletion.emitted completionSteps,
      Compiler.canonical modulus (Compiler.unoutline '''+str(copy)+''' actual.a) = Compiler.canonical modulus expected.a ∧
      Compiler.canonical modulus (Compiler.unoutline '''+str(copy)+''' actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  simp only [RuntimeTransferNoteSpend.rawRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in raw)+'\n')
    for i in raw:
        out.append(f'''  · refine ⟨{expected[i]}, ?_, by decide, by decide⟩
    simp [completionSteps,CompilerCompletion.emitted,CompilerCompletion.Step.rows,
      ScalarCompletion.productRows,Compiler.subtract,scaleLinear,output0,output1,output2]
''')
    out.append('''def RequiredRepresents {F : Type} [Field F] (rho : Nat → F) (v : NoteSpendCompletion.Values F) : Prop :=
  eval rho requiredAmount = v.amount ∧ eval rho requiredNullifier = v.nullifier ∧
  eval rho requiredRealNullifier = v.realNullifier ∧ eval rho requiredComputedAnchor = v.computedAnchor ∧
  eval rho requiredAnchor = v.anchor

theorem legal_steps {F : Type} [Field F] (rho : Nat → F) (one : rho 0 = 1)
    (required optional : NoteSpendCompletion.Values F)
    (requiredInput : RequiredRepresents rho required) (requiredReal : required.dummy = false)
    (requiredMeaning : required.Legal) (optionalInput : inputs.Represents rho optional)
    (optionalMeaning : optional.Legal) : CompilerCompletion.Legal rho completionSteps := by
  have requiredNF : required.nullifier = required.realNullifier := by
    simpa only [requiredReal,Bool.false_eq_true,if_false] using requiredMeaning.1
  have requiredRoot := requiredMeaning.2.1 requiredReal
  rcases requiredInput with ⟨amount,nf,realNF,root,anchor⟩
  have realNFEquation : eval rho requiredRealNullifier = eval rho requiredNullifier := by
    rw [realNF,nf,requiredNF]
  have realRootEquation : eval rho requiredComputedAnchor = eval rho requiredAnchor := by
    rw [root,anchor,requiredRoot]
''')
    out.append('  have equations := NoteSpendCompletion.source_equations inputs rho optional one optionalInput optionalMeaning '+
               ' '.join(str(c) for c in plan['writes'])+'\n')
    for i in range(3):
        projection=('.1','.2.1','.2.2')[i]
        out.append(f'''  have equation{i} : eval rho left{i} * eval rho right{i} = eval rho target{i} := by
    simpa only [inputs,NoteSpendCompletion.selector,NoteSpendCompletion.anchorGate,
      NoteSpendCompletion.amountGate,NoteSpendCompletion.Gate.Equation,left{i},right{i},target{i},mul_comm]
      using equations{projection}
  have productAssertion{i} : eval (completeAssignment rho) output{i} = eval (completeAssignment rho) target{i} :=
    (materialized{i} rho).trans (equation{i}.trans (source_preserved rho target{i} (by decide)).symm)
''')
    out.append('''  have booleanEquation : eval (completeAssignment rho) dummy * eval (completeAssignment rho) dummy =
      eval (completeAssignment rho) dummy := by
    have dummyValue : eval rho dummy = optional.bit := optionalInput.1
    rw [source_preserved rho dummy (by decide),dummyValue]
    exact NoteSpendCompletion.branch_boolean optional
  have requiredNFEquation : eval (completeAssignment rho) requiredRealNullifier = eval (completeAssignment rho) requiredNullifier := by
    rw [source_preserved rho requiredRealNullifier (by decide),source_preserved rho requiredNullifier (by decide)]
    exact realNFEquation
  have requiredAnchorEquation : eval (completeAssignment rho) requiredComputedAnchor = eval (completeAssignment rho) requiredAnchor := by
    rw [source_preserved rho requiredComputedAnchor (by decide),source_preserved rho requiredAnchor (by decide)]
    exact realRootEquation
  simp only [completionSteps,CompilerCompletion.Legal,CompilerCompletion.Step.Legal,CompilerCompletion.Step.run]
''')
    assertion_proofs=[('requiredNFEquation'+('.symm' if certs['required.nullifier']['reverse'] else '')),
                      ('requiredAnchorEquation'+('.symm' if certs['required.anchor']['reverse'] else '')),
                      'booleanEquation']
    assertion_proofs+=['productAssertion'+str(i)+('.symm' if certs['optional.'+name]['reverse'] else '')
                       for i,name in enumerate(('selected','anchor','amount'))]
    out.append('  exact ⟨trivial,trivial,trivial,'+','.join(assertion_proofs)+',trivial,trivial⟩\n')
    out.append(f'''theorem complete_two_spends {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (linked : rho {copy} = rho 0)
    (required optional : NoteSpendCompletion.Values F)
    (requiredInput : RequiredRepresents rho required) (requiredReal : required.dummy = false)
    (requiredMeaning : required.Legal) (optionalInput : inputs.Represents rho optional)
    (optionalMeaning : optional.Legal) :
    Satisfies (completeAssignment rho) RuntimeTransferNoteSpend.rawRows ∧
      (∀ column ∈ kept, completeAssignment rho column = rho column) := by
  have result := CompilerCompletion.original_rows_complete rho completionSteps kept
    RuntimeTransferNoteSpend.rawRows {copy} completion_ordered
    (legal_steps rho one required optional requiredInput requiredReal requiredMeaning optionalInput optionalMeaning)
    (by decide) (by decide) linked completion_coverage
  rw [completion_run] at result
  exact result

-- These are finite local original-row construction proofs, not a full circuit
-- assignment or a hash/Merkle witness existence certificate.
#print axioms completion_ordered_checked
#print axioms completion_ordered
#print axioms completion_run
#print axioms kept_preserved
#print axioms source_preserved
#print axioms materialized0
#print axioms materialized1
#print axioms materialized2
#print axioms completion_coverage
#print axioms legal_steps
#print axioms complete_two_spends
end ShielddSecurity.RuntimeTransferNoteSpendCompletion
''')
    return _signature_audits(''.join(out))
