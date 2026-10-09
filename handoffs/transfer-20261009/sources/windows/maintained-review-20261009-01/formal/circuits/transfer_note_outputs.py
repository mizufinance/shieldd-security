"""Exact two-output LCs and ordinary binding/inverse rows at native note hooks.

Hash, recovery/group and receiver-address semantics remain separately captured
obligations. This module neither invents a hash equation nor requires change to
be nonzero. Runtime qualification must compare two full ordinary relations and
repeat observations before accepted flags are supplied.
"""
import hashlib
from . import transfer_relation as relation,transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical,combine,source_index
from .generate_hash_round import linear,_signature_audits

SCOPE='two ordered receiver/change source roles and actual bindings/inverse/ranges; hash/recovery/native joins open'


def inspect_metadata(data,accepted_roles):
    if not isinstance(data,bytes) or len(data)>1024*1024:raise relation.RelationError('output metadata byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
        'ordinary_full_ordered_rows_equal','repeated_observations_equal','outputs','expressions'}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=('shieldd-transfer-note-output-v1','transfer',SCOPE):
        raise relation.RelationError('output closed schema/scope')
    accepted=accepted_roles['metadata']
    if (any(obj[k]!=accepted[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')) or
        obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('output accepted relation identity/pending mismatch')
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],512,'note-output')
    required=set();bits_seen=set();witnesses=set();parsed=[]
    def value(ref,witness=False):
        if not isinstance(ref,dict) or set(ref)!={'source'}:raise relation.RelationError('output actual source reference required')
        handle=source_index(ref['source']);required.add(handle)
        if handle not in observed:raise relation.RelationError('output source LC coverage')
        if witness:
            if handle[0]!=1 or handle in witnesses:raise relation.RelationError('output witness role alias/shape')
            witnesses.add(handle)
        return observed[handle]
    if not isinstance(obj['outputs'],list) or len(obj['outputs'])!=2:raise relation.RelationError('output exacttwo inventory')
    fields={'receiver','note','amount_bits','receiver_inverse','computed_commitment','commitment','capsule','capsule_commitment','payload_key'}
    for slot,output in enumerate(obj['outputs']):
        if not isinstance(output,dict) or set(output)!=fields or type(output['receiver']) is not bool or output['receiver']!=(slot==0):
            raise relation.RelationError('output receiver/change exact order/shape')
        for name,width in (('note',8),('capsule',7),('payload_key',2)):
            if not isinstance(output[name],list) or len(output[name])!=width:raise relation.RelationError('output exact native field arity')
        note=tuple(value(ref,witness=i in (0,1,7)) for i,ref in enumerate(output['note']))
        if output['note'][2]!=accepted['caller']['asset'] or slot==1 and output['note'][3:7]!=accepted['caller']['address']:
            raise relation.RelationError('output asset/change-address caller source mismatch')
        inverse=output['receiver_inverse']
        if (slot==0 and inverse is None) or (slot==1 and inverse is not None):raise relation.RelationError('output inverse receiver-only policy')
        inverse=value(inverse,witness=True) if inverse is not None else None
        bits=output['amount_bits']
        if not isinstance(bits,list) or len(bits)!=128:raise relation.RelationError('output128 bit inventory')
        handles=tuple(source_index(bit) for bit in bits)
        if len(set(handles))!=128 or any(h[0]!=1 or h in bits_seen for h in handles):
            raise relation.RelationError('output bit witness alias/shape')
        bits_seen.update(handles);required.update(handles)
        if not set(handles)<=set(observed):raise relation.RelationError('output bit source LC coverage')
        columns=[observed[h][0][0] for h in handles]
        if columns!=list(range(columns[0],columns[0]+128)):raise relation.RelationError('output bit physical contiguity')
        parsed.append(dict(note=note,columns=columns,inverse=inverse,
            computed=value(output['computed_commitment']),commitment=value(output['commitment'],witness=True),
            capsule=tuple(value(ref) for ref in output['capsule']),capsule_commitment=value(output['capsule_commitment'],witness=True),
            payload=tuple(value(ref) for ref in output['payload_key'])))
    if obj['outputs'][0]['payload_key']!=obj['outputs'][1]['payload_key']:
        raise relation.RelationError('output shared payload source mismatch')
    if bits_seen&witnesses or set(observed)!=required:raise relation.RelationError('output exact source coverage/bit role collision')
    bit_columns={observed[h][0][0] for h in bits_seen}
    for h,lc in observed.items():
        if h not in bits_seen and any(c in bit_columns for c,_ in lc):raise relation.RelationError('output owned range bits overlap source role')
        if h in accepted_roles['observed'] and lc!=accepted_roles['observed'][h]:
            raise relation.RelationError('output/caller shared LC mismatch')
    return dict(metadata=obj,observed=observed,outputs=parsed,metadata_sha256=hashlib.sha256(data).hexdigest())


def extract(data,stream,accepted_roles):
    checked=inspect_metadata(data,accepted_roles);obj=checked['metadata'];copy=obj['constant_copy']
    outline=lambda terms:canonical((copy if c==0 else c,v) for c,v in terms)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    for slot,output in enumerate(checked['outputs']):
        for role,left,right in [('note',output['computed'],output['commitment']),('recovery',output['capsule_commitment'],output['note'][7])]:
            required[(outline(combine(left,right,-1)),())]=[f'output{slot}.{role}-binding']
    amount=checked['outputs'][0]['note'][1];inverse=checked['outputs'][0]['inverse']
    product=('receiver-nonzero',outline(combine(inverse,amount,-1)),outline(combine(inverse,amount)),None,((copy,1),))
    result=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],required,[product],[],label='note-output')
    result.update(metadata_sha256=checked['metadata_sha256'],scope='actual two-output binding/inverse rows; amount ranges and hash/recovery semantics separate')
    return result


def certificates(data,extracted,accepted_roles):
    checked=inspect_metadata(data,accepted_roles);raw,rows=arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    used=set();bindings=[]
    for output in checked['outputs']:
        for left,right in ((output['computed'],output['commitment']),(output['capsule_commitment'],output['note'][7])):
            delta=combine(left,right,-1);matches=[i for i,row in rows.items() if row in ((delta,()),(canonical((c,-v) for c,v in delta),()))]
            if len(matches)!=1:raise relation.RelationError('output exact binding assertion missing/ambiguous')
            used.update(matches);bindings.append((left,right))
    output=checked['outputs'][0];inverse=arithmetic.quotient_certificate(((0,1),),output['note'][1],output['inverse'],rows)
    if inverse['kind']!='product' or len(inverse['rows'])!=3:raise relation.RelationError('output inverse needs actual materialized product/assertion')
    used.update(inverse['rows']);copy=checked['metadata']['constant_copy']
    used.add(next(i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())))
    if used!=set(raw):raise relation.RelationError('output exact binding/inverse physical row coverage')
    return dict(checked=checked,raw=raw,rows=rows,bindings=bindings,inverse=inverse)


def generate(data,extracted,accepted_roles):
    selected=certificates(data,extracted,accepted_roles);checked=selected['checked'];copy=checked['metadata']['constant_copy']
    cert=selected['inverse'];source=f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferNoteOutputBindings
-- Exact ordinary relation {checked['metadata']['relation_digest']}; only8 selected binding/inverse rows.
-- Receiver128 range, both NOTE15/8 hashes and complete recovery semantics remain separate joins.
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in selected['raw'].values())+']\n'
    source+=f'''def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def amount : Linear := {linear(cert['denominator'])}
def inverse : Linear := {linear(cert['quotient'])}
def product : Linear := {linear(cert['output'])}
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
'''
    for slot in range(2):
        for offset,role in enumerate(('note','recovery')):
            left,right=selected['bindings'][2*slot+offset]
            direct=(combine(left,right,-1),()) in selected['rows'].values()
            first,second=(left,right) if direct else (right,left)
            assertion=f'Compiler.checked_assertion_sound rho rows {linear(first)} {linear(second)} normalized (by decide)'
            if not direct: assertion='('+assertion+').symm'
            source+=f'''theorem output{slot}_{role}_binding {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : eval rho {linear(left)} = eval rho {linear(right)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  exact {assertion}
'''
    left,right=('amount','inverse') if cert['swapped'] else ('inverse','amount')
    direct=(combine(cert['output'],((0,1),),-1),()) in selected['rows'].values()
    asserted='Compiler.checked_assertion_sound rho rows product [(0,1)] normalized (by decide)' if direct else '(Compiler.checked_assertion_sound rho rows [(0,1)] product normalized (by decide)).symm'
    source+=f'''theorem receiver_inverse {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho inverse * eval rho amount = 1 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have multiplied := Compiler.checked_product_sound rho rows {left} {right} product
    {linear(cert['auxiliary'])} four normalized (by decide) (by decide)
  have asserted := {asserted}
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,one,add_zero]
  simpa only [asserted,unit,mul_comm] using multiplied.symm
theorem receiver_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho amount ≠ 0 := by
  intro zero
  have equation := receiver_inverse rho one four satisfied
  rw [zero,mul_zero] at equation
  exact zero_ne_one equation
'''
    for export in ('constantLink','output0_note_binding','output0_recovery_binding','output1_note_binding','output1_recovery_binding',
                   'receiver_inverse','receiver_nonzero'):source+=f'#print axioms {export}\n'
    return _signature_audits(source+'end ShielddSecurity.RuntimeTransferNoteOutputBindings\n')


def range_boundary(data,accepted_roles,slot):
    slot=relation.natural(slot,2);checked=inspect_metadata(data,accepted_roles)
    output=checked['outputs'][slot];value=output['note'][1]
    if len(value)!=1 or value[0][1]!=1:raise relation.RelationError('output range actual unit amount witness')
    columns=output['columns'];weighted=canonical((column,2**i) for i,column in enumerate(columns))
    return dict(checked=checked,columns=columns,value=value[0][0],width=128,weighted=weighted,slot=slot,kind='amount')


def extract_range(data,stream,accepted_roles,slot):
    selected=range_boundary(data,accepted_roles,slot);obj=selected['checked']['metadata'];copy=obj['constant_copy']
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    for i,column in enumerate(selected['columns']):required[(((column,1),),((column,1),))]=['bit.'+str(i)]
    required[(combine(selected['weighted'],((selected['value'],1),),-1),())]=['reconstruction']
    result=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],required,[],[],label='output-amount128')
    result.update(metadata_sha256=hashlib.sha256(data).hexdigest(),slot=slot,kind='amount',scope='one actual output128 range only; NOTE/recovery/native joins open')
    return result


def generate_range(data,extracted,accepted_roles,slot):
    from .transfer_note_ranges import _generate_boundary
    selected=range_boundary(data,accepted_roles,slot)
    handles={tuple(h) for h in selected['checked']['metadata']['outputs'][slot]['amount_bits']}
    return _generate_boundary(data,extracted,accepted_roles,selected,slot,'amount',handles,
                              f'RuntimeTransferOutput{slot}AmountRange')


def receiver_completion_plan(data,extracted,accepted_roles):
    """Own only the exact receiver inverse/product/auxiliary materializations.

The four NOTE/recovery binding assertions need their preceding hash/capsule
constructions and are deliberately not claimed to survive these writes.
"""
    selected=certificates(data,extracted,accepted_roles);cert=selected['inverse']
    checked=selected['checked'];obj=checked['metadata'];copy=obj['constant_copy']
    inverse=cert['quotient'];auxiliary=cert['auxiliary']
    if cert['swapped'] or len(inverse)!=1 or inverse[0][1]!=1 or len(auxiliary)!=1 or auxiliary[0][1]!=1:
        raise relation.RelationError('output completion requires exact quotient-first unit inverse/auxiliary')
    quotient=inverse[0][0];aux=auxiliary[0][0]
    inverse_handle=source_index(obj['outputs'][0]['receiver_inverse']['source'])
    for output in obj['outputs']:
        refs=[*output['note'],*output['capsule'],*output['payload_key'],output['computed_commitment'],
              output['commitment'],output['capsule_commitment']]
        if any(source_index(ref['source'])==inverse_handle for ref in refs):
            raise relation.RelationError('output completion inverse aliases readonly source role')
    kept=[lc for handle,lc in sorted(checked['observed'].items()) if handle!=inverse_handle]
    kept.extend(lc for _,lc in sorted(accepted_roles['observed'].items()))
    protected={0,1,2,copy,quotient,aux}|{c for lc in kept for c,_ in lc}
    candidates=[c for c,v in cert['output'] if v==1 and c not in protected]
    if len(candidates)!=1:raise relation.RelationError('output completion fresh unit product pivot absent/ambiguous')
    product=candidates[0];writes=[quotient,product,aux]
    remainder=tuple((c,v) for c,v in cert['output'] if c!=product)
    if len(set(writes))!=3 or any(c in writes for lc in kept for c,_ in lc) or any(
            c in writes for c,_ in ((0,1),)+cert['denominator']+remainder):
        raise relation.RelationError('output completion owned writes overlap shared/readonly source')
    output=canonical(((product,1),)+remainder)
    expected=[(combine(inverse,cert['denominator'],-1),((aux,1),)),
        (combine(inverse,cert['denominator']),combine(((aux,1),),output,4)),
        (combine(output,((0,1),),-1),())]
    indices=cert['rows']
    actual=[selected['rows'][i] for i in indices]
    if len(actual)!=len(expected) or any(b!=d or a not in (c,canonical((column,-value) for column,value in c)) for (a,b),(c,d) in zip(actual,expected)):
        raise relation.RelationError('output completion exact original quotient constructor/orientation differs')
    signed=actual!=expected
    return dict(selected=selected,quotient=quotient,product=product,auxiliary=aux,
        writes=writes,remainder=remainder,kept=kept,signed=signed,
        raw={i:selected['raw'][i] for i in indices})


def generate_receiver_completion(data,extracted,accepted_roles):
    plan=receiver_completion_plan(data,extracted,accepted_roles)
    checked=plan['selected']['checked'];copy=checked['metadata']['constant_copy']
    q,p,a=(plan[key] for key in ('quotient','product','auxiliary'))
    signed_check = ' ∨ Compiler.canonical modulus (Compiler.unoutline '+str(copy)+' actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)' if plan['signed'] else ''
    extra_import = 'import ShielddSecurity.CompilerSignedCompletion\n' if plan['signed'] else ''
    source=f'''import ShielddSecurity.GroupRowCompletion
{extra_import}
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeTransferOutputReceiverCompletion
-- Only3 actual receiver inverse rows; amount128 and full NOTE/recovery construction separate.
-- Relation identity: {checked['metadata']['relation_digest']}.
def modulus : Nat := {relation.MODULUS}
def amount : Linear := {linear(plan['selected']['inverse']['denominator'])}
def remainder : Linear := {linear(plan['remainder'])}
def ownedWrites : List Nat := {plan['writes']}
def kept : List Linear := [{', '.join(linear(lc) for lc in plan['kept'])}]
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(left)+','+linear(right)+'⟩' for left,right in plan['raw'].values())+f''']
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient rho [(0,1)] amount remainder {q} {p} {a}

theorem coverage_checked : rawRows.all (fun actual =>
    (GroupRowCompletion.quotientRows [(0,1)] amount remainder {q} {p} {a}).any (fun expected =>
      decide ((Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a{signed_check}) ∧
        Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈
    GroupRowCompletion.quotientRows [(0,1)] amount remainder {q} {p} {a},
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a{signed_check}) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  GroupRowCompletion.extend_preserves rho [(0,1)] amount remainder {q} {p} {a} column outside
theorem kept_checked : kept.all (fun terms => terms.all (fun term => decide (term.1 ∉ ownedWrites))) = true := by decide
theorem kept_preserved {{F : Type}} [Field F] (rho : Nat → F) :
    ∀ terms ∈ kept, eval (completeAssignment rho) terms = eval rho terms := by
  intro terms member
  apply eval_agrees
  intro term present
  exact preserves rho term.1 (of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp kept_checked) terms member)) term present))

theorem complete_rows {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) (legal : eval rho amount ≠ 0) :
    Satisfies (completeAssignment rho) rawRows :=
  GroupRowCompletion.original_rows_complete rho [(0,1)] amount remainder {q} {p} {a}
    (by decide) (by decide) (by decide) (by decide) legal rawRows {copy}
    (by decide) (by decide) linked coverage

theorem inverse_value {{F : Type}} [Field F] (rho : Nat → F) (one : rho 0 = 1) :
    completeAssignment rho {q} = (eval rho amount)⁻¹ := by
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,one,add_zero]
  change GroupRowCompletion.extendQuotient rho [(0,1)] amount remainder {q} {p} {a} {q} = _
  rw [GroupRowCompletion.quotient_value,unit,one_div]

theorem complete_receiver {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (legal : eval rho amount ≠ 0) :
    Satisfies (completeAssignment rho) rawRows ∧
      completeAssignment rho {q} = (eval rho amount)⁻¹ ∧
      (∀ column, column ∉ ownedWrites → completeAssignment rho column = rho column) :=
  ⟨complete_rows rho linked legal,inverse_value rho one,preserves rho⟩
'''
    if plan['signed']:
        old=f"""    Satisfies (completeAssignment rho) rawRows :=
  GroupRowCompletion.original_rows_complete rho [(0,1)] amount remainder {q} {p} {a}
    (by decide) (by decide) (by decide) (by decide) legal rawRows {copy}
    (by decide) (by decide) linked coverage"""
        new=f"""    Satisfies (completeAssignment rho) rawRows := by
  have completed := GroupRowCompletion.extend_complete rho [(0,1)] amount remainder {q} {p} {a}
    (by decide) (by decide) (by decide) (by decide) legal
  have copyLink : completeAssignment rho {copy} = completeAssignment rho 0 := by
    rw [preserves rho {copy} (by decide),preserves rho 0 (by decide),linked]
  exact CompilerSignedCompletion.original_rows (completeAssignment rho)
    (GroupRowCompletion.quotientRows [(0,1)] amount remainder {q} {p} {a}) rawRows {copy}
    copyLink completed coverage"""
        if source.count(old)!=1:raise relation.RelationError('receiver signed proof source anchor')
        source=source.replace(old,new,1)
    for export in ('coverage_checked','coverage','preserves','kept_checked','kept_preserved',
                   'complete_rows','inverse_value','complete_receiver'):
        source+=f'#print axioms {export}\n'
    return _signature_audits(source+'end ShielddSecurity.RuntimeTransferOutputReceiverCompletion\n')
