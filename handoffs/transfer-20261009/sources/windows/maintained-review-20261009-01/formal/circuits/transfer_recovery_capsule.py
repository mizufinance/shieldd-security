"""Exact recovery source roles and original linear binding rows.

Scalar canonicality, both EPK inverse gadgets, fixed/variable multiplication,
and native hash semantics remain mandatory separate joins.
"""
import hashlib
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from . import transfer_note_outputs as outputs, transfer_note_output_bindings as bindings
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index
from .generate_hash_round import linear, _signature_audits

SCOPE = 'two output recovery source roles including both EPK inverses; scalar/group/hash/native joins open'
ROLES = ('epk-x', 'epk-y', 'c2', 'confirmation', 'encrypted-amount', 'encrypted-blinding')


def inspect_metadata(data, output_data, accepted_roles):
    accepted = outputs.inspect_metadata(output_data, accepted_roles)
    if not isinstance(data, bytes) or len(data) > 1024 * 1024:
        raise relation.RelationError('recovery metadata byte bound')
    obj = relation.record(data)
    keys = {'schema', 'family', 'scope', 'relation_digest', 'domain_size', 'full_rows', 'constant_copy',
            'ordinary_full_ordered_rows_equal', 'repeated_observations_equal', 'capsules', 'expressions'}
    if set(obj) != keys or (obj['schema'], obj['family'], obj['scope']) != (
            'shieldd-transfer-recovery-capsule-roles-v1', 'transfer', SCOPE):
        raise relation.RelationError('recovery closed schema/scope')
    if (any(obj[k] != accepted['metadata'][k] for k in
            ('relation_digest', 'domain_size', 'full_rows', 'constant_copy')) or
            obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('recovery accepted relation identity/pending mismatch')
    observed = _expressions(obj['expressions'], obj['domain_size'], obj['constant_copy'], 1024, 'recovery')
    required = set(); bits_seen = set(); private = set(); parsed = []

    def value(ref, witness=False):
        if not isinstance(ref, dict) or set(ref) != {'source'}:
            raise relation.RelationError('recovery actual source reference required')
        handle = source_index(ref['source']); required.add(handle)
        if handle not in observed:
            raise relation.RelationError('recovery source LC coverage')
        if witness:
            if handle[0] != 1 or handle in private:
                raise relation.RelationError('recovery private witness alias/shape')
            private.add(handle)
        return observed[handle]

    def array(refs, width):
        if not isinstance(refs, list) or len(refs) != width:
            raise relation.RelationError('recovery exact role arity')
        return tuple(value(ref) for ref in refs)

    fields = {'payload_key', 'amount', 'blinding', 'randomizer', 'bits', 'seed', 'capsule', 'commitment',
              'computed_epk', 'shared', 'secret', 'computed_c2', 'computed_confirmation', 'amount_stream',
              'computed_amount', 'blinding_stream', 'computed_blinding', 'epk_inverse', 'plaintext_inverse'}
    if not isinstance(obj['capsules'], list) or len(obj['capsules']) != 2:
        raise relation.RelationError('recovery exacttwo inventory')
    for slot, entry in enumerate(obj['capsules']):
        if not isinstance(entry, dict) or set(entry) != fields:
            raise relation.RelationError('recovery closed capsule shape')
        out = accepted['metadata']['outputs'][slot]
        if (entry['capsule'] != out['capsule'] or entry['commitment'] != out['capsule_commitment'] or
                entry['payload_key'] != out['payload_key'] or entry['amount'] != out['note'][1] or
                entry['blinding'] != out['note'][0]):
            raise relation.RelationError('recovery exact output/capsule/NOTE source roles changed')
        cap = array(entry['capsule'], 7); array(entry['payload_key'], 2)
        epk = array(entry['computed_epk'], 2); array(entry['shared'], 2)
        amount = value(entry['amount']); blinding = value(entry['blinding']); value(entry['commitment'])
        seed = value(entry['seed'], True); randomizer = value(entry['randomizer'], True)
        inverses = (value(entry['epk_inverse'], True), value(entry['plaintext_inverse'], True))
        secret = value(entry['secret']); c2 = value(entry['computed_c2'])
        confirmation = value(entry['computed_confirmation'])
        amount_stream = value(entry['amount_stream']); computed_amount = value(entry['computed_amount'])
        blinding_stream = value(entry['blinding_stream']); computed_blinding = value(entry['computed_blinding'])
        if (c2, computed_amount, computed_blinding) != (
                combine(seed, secret), combine(amount, amount_stream), combine(blinding, blinding_stream)):
            raise relation.RelationError('recovery exact computed addition LC changed')
        bits = entry['bits']
        if not isinstance(bits, list) or len(bits) != 252:
            raise relation.RelationError('recovery252 bit inventory')
        handles = tuple(source_index(bit) for bit in bits)
        if len(set(handles)) != 252 or any(h[0] != 1 or h in bits_seen or h in private for h in handles):
            raise relation.RelationError('recovery bit/private witness alias')
        bits_seen.update(handles); required.update(handles)
        if not set(handles) <= set(observed):
            raise relation.RelationError('recovery bit LC coverage')
        columns = [observed[h][0][0] for h in handles]
        if columns != list(range(columns[0], columns[0] + 252)):
            raise relation.RelationError('recovery bit physical contiguity')
        pairs = tuple(zip(ROLES, (*epk, c2, confirmation, computed_amount, computed_blinding),
                          (cap[0], cap[1], cap[2], cap[4], cap[5], cap[6])))
        parsed.append(dict(pairs=pairs, inverses=inverses, epk=cap[:2], bits=columns, randomizer=randomizer))
    external = set(accepted['observed']) | set(accepted_roles['observed'])
    if private & (bits_seen | external) or bits_seen & external or set(observed) != required:
        raise relation.RelationError('recovery exact source coverage/private bits collision')
    for handle, lc in observed.items():
        for owner in (accepted['observed'], accepted_roles['observed']):
            if handle in owner and lc != owner[handle]:
                raise relation.RelationError('recovery shared output/caller LC mismatch')
    return dict(metadata=obj, observed=observed, capsules=parsed, outputs=accepted,
                metadata_sha256=hashlib.sha256(data).hexdigest())


def extract_bindings(data, stream, output_data, accepted_roles):
    checked = inspect_metadata(data, output_data, accepted_roles); obj = checked['metadata']; copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c, v) for c, v in lc)
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy']}
    for slot, capsule in enumerate(checked['capsules']):
        for role, left, right in capsule['pairs']:
            key = (outline(combine(left, right, -1)), ())
            if key in required:
                raise relation.RelationError('recovery duplicate actual binding equation')
            required[key] = [f'recovery{slot}.{role}']
    result = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
        required, [], [], label='recovery-bindings')
    result.update(metadata_sha256=checked['metadata_sha256'],
        scope='12 actual recovery assertions; group/hash/inverse/scalar semantics separate')
    return result


def certificates(data, extracted, output_data, accepted_roles):
    checked = inspect_metadata(data, output_data, accepted_roles)
    raw, rows = arithmetic.normalize_selection(extracted, checked['metadata'], checked['metadata_sha256'])
    used = set(); pairs = []
    for slot, capsule in enumerate(checked['capsules']):
        for role, left, right in capsule['pairs']:
            delta = combine(left, right, -1); opposite = canonical((c, -v) for c, v in delta)
            matches = [i for i, row in rows.items() if row in ((delta, ()), (opposite, ()))]
            if len(matches) != 1:
                raise relation.RelationError('recovery exact assertion missing/ambiguous')
            used.update(matches); pairs.append((slot, role, left, right, matches[0]))
    copy = checked['metadata']['constant_copy']
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(links) != 1 or used | set(links) != set(raw):
        raise relation.RelationError('recovery exact assertion/copy coverage')
    return dict(checked=checked, raw=raw, rows=rows, pairs=pairs)


def extract_inverses(data, stream, output_data, accepted_roles):
    checked = inspect_metadata(data, output_data, accepted_roles); obj = checked['metadata']; copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c, v) for c, v in lc)
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy']}
    products = []
    for slot, capsule in enumerate(checked['capsules']):
        for occurrence, inverse in enumerate(capsule['inverses']):
            x = capsule['epk'][0]
            products.append((f'recovery{slot}.epk-inverse{occurrence}', outline(combine(inverse, x, -1)),
                outline(combine(inverse, x)), None, ((copy, 1),)))
    result = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
        required, products, [], label='recovery-epk-inverses')
    result.update(metadata_sha256=checked['metadata_sha256'],
        scope='four distinct actual EPK inverse triples; nonzero/subgroup/native semantics separate')
    return result


def inverse_certificates(data, extracted, output_data, accepted_roles):
    checked = inspect_metadata(data, output_data, accepted_roles)
    raw, rows = arithmetic.normalize_selection(extracted, checked['metadata'], checked['metadata_sha256'])
    used = set(); inverses = []
    for slot, capsule in enumerate(checked['capsules']):
        for occurrence, inverse in enumerate(capsule['inverses']):
            cert = arithmetic.quotient_certificate(((0, 1),), capsule['epk'][0], inverse, rows)
            if cert['kind'] != 'product' or len(cert['rows']) != 3 or used & set(cert['rows']):
                raise relation.RelationError('recovery distinct EPK inverse triple coverage')
            used.update(cert['rows']); inverses.append((slot, occurrence, cert))
    copy = checked['metadata']['constant_copy']
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(links) != 1 or used | set(links) != set(raw):
        raise relation.RelationError('recovery exact inverse/copy coverage')
    return dict(checked=checked, raw=raw, rows=rows, inverses=inverses)


def completion_plan(data, extracted, output_data, accepted_roles, slot, role):
    slot = relation.natural(slot, 2)
    if role not in ROLES:
        raise relation.RelationError('recovery exact completion role')
    selected = certificates(data, extracted, output_data, accepted_roles); checked = selected['checked']; obj = checked['metadata']
    _, _, computed, target_lc, index = next(p for p in selected['pairs'] if p[:2] == (slot, role))
    offset = dict(zip(ROLES, (0, 1, 2, 4, 5, 6)))[role]
    target_ref = source_index(obj['capsules'][slot]['capsule'][offset]['source'])
    if target_ref[0] != 1 or target_lc != ((target_ref[1] + 3, 1),):
        raise relation.RelationError('recovery exact supplied target witness')
    target = target_lc[0][0]; readonly = {0, 1, 2, obj['constant_copy']}
    for owner in (checked['observed'], checked['outputs']['observed'], accepted_roles['observed']):
        for handle, lc in owner.items():
            if handle != target_ref:
                readonly.update(c for c, _ in lc)
    if target in readonly or any(c == target for c, _ in computed):
        raise relation.RelationError('recovery target aliases shared/source column')
    return dict(checked=checked, computed=computed, target=target, copy=obj['constant_copy'], raw_row=selected['raw'][index],
        original_row=index, kept=sorted(readonly), writes=[target],
        scope='one actual recovery equality witness; preceding group/hash and surrounding rows separate')


def generate_completion(data, extracted, output_data, accepted_roles, slot, role):
    plan = completion_plan(data, extracted, output_data, accepted_roles, slot, role)
    return bindings._source(plan, f'RuntimeTransferRecovery{slot}{role.title().replace("-", "")}BindingCompletion')


def _sound_header(selected, name):
    checked=selected['checked'];copy=checked['metadata']['constant_copy']
    source=f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact selected ordinary rows; native group/hash/scalar claims remain separate.
-- Relation {checked['metadata']['relation_digest']}.
def modulus : Nat := {relation.MODULUS}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in selected['raw'].values())+f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
'''
    return source,copy


def generate_sound(data, extracted, output_data, accepted_roles):
    selected=certificates(data,extracted,output_data,accepted_roles)
    name='RuntimeTransferRecoveryBindings';source,copy=_sound_header(selected,name);exports=['constantLink']
    for slot,role,left,right,index in selected['pairs']:
        export=f'recovery{slot}_{role.replace("-","_")}_binding';exports.append(export)
        forward=selected['rows'][index]==(combine(left,right,-1),())
        a,b=(left,right) if forward else (right,left)
        proof=f'Compiler.checked_assertion_sound rho rows {linear(a)} {linear(b)} normalized (by decide)'
        proof=proof if forward else '('+proof+').symm'
        source+=f'''theorem {export} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : eval rho {linear(left)} = eval rho {linear(right)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  exact {proof}
'''
    for export in exports:source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def generate_inverse_sound(data, extracted, output_data, accepted_roles):
    selected=inverse_certificates(data,extracted,output_data,accepted_roles)
    name='RuntimeTransferRecoveryEpkInverses';source,copy=_sound_header(selected,name);exports=['constantLink']
    for slot,occurrence,cert in selected['inverses']:
        prefix=f'recovery{slot}_occurrence{occurrence}';exports.extend((prefix+'_inverse',prefix+'_nonzero'))
        q,x=cert['quotient'],cert['denominator'];left,right=(x,q) if cert['swapped'] else (q,x)
        forward=selected['rows'][cert['rows'][-1]]==(combine(cert['output'],((0,1),),-1),())
        a,b=(cert['output'],((0,1),)) if forward else (((0,1),),cert['output'])
        assertion=f'Compiler.checked_assertion_sound rho rows {linear(a)} {linear(b)} normalized (by decide)'
        assertion=assertion if forward else '('+assertion+').symm'
        source+=f'''theorem {prefix}_inverse {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(q)} * eval rho {linear(x)} = 1 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have multiplied := Compiler.checked_product_sound rho rows {linear(left)} {linear(right)} {linear(cert['output'])}
    {linear(cert['auxiliary'])} four normalized (by decide) (by decide)
  have asserted := {assertion}
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,one,add_zero]
  simpa only [asserted,unit,mul_comm] using multiplied.symm
theorem {prefix}_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(x)} ≠ 0 := by
  intro zero
  have equation := {prefix}_inverse rho one four satisfied
  rw [zero,mul_zero] at equation
  exact zero_ne_one equation
'''
    for export in exports:source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def inverse_completion_plan(data, extracted, output_data, accepted_roles, slot, occurrence):
    slot=relation.natural(slot,2);occurrence=relation.natural(occurrence,2)
    selected=inverse_certificates(data,extracted,output_data,accepted_roles)
    cert=next(c for s,o,c in selected['inverses'] if (s,o)==(slot,occurrence))
    plan=arithmetic.completion_certificate(cert,selected['rows'])
    if plan is None:raise relation.RelationError('recovery exact quotient constructor shape unsupported')
    checked=selected['checked'];copy=checked['metadata']['constant_copy'];writes=[plan[k] for k in ('quotient','product','auxiliary')]
    key='epk_inverse' if occurrence==0 else 'plaintext_inverse'
    own=source_index(checked['metadata']['capsules'][slot][key]['source'])
    kept=[((0,1),),((1,1),),((2,1),),((copy,1),)]
    for owner in (checked['observed'],checked['outputs']['observed'],accepted_roles['observed']):
        kept.extend(lc for handle,lc in sorted(owner.items()) if handle!=own)
    if any(c in writes for lc in kept for c,_ in lc):
        raise relation.RelationError('recovery inverse writes alias shared/readonly source')
    return dict(plan,checked=checked,slot=slot,occurrence=occurrence,writes=writes,kept=list(dict.fromkeys(kept)),
                raw={i:selected['raw'][i] for i in plan['rows']})


def generate_inverse_completion(data, extracted, output_data, accepted_roles, slot, occurrence):
    plan=inverse_completion_plan(data,extracted,output_data,accepted_roles,slot,occurrence)
    q,p,a=(plan[k] for k in ('quotient','product','auxiliary'));copy=plan['checked']['metadata']['constant_copy']
    name=f'RuntimeTransferRecovery{slot}EpkInverse{occurrence}Completion'
    source=f'''import ShielddSecurity.GroupRowCompletion
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Only3 exact EPK inverse rows; native EPK nonidentity/group/scalar joins separate.
-- Relation {plan['checked']['metadata']['relation_digest']}.
def modulus : Nat := {relation.MODULUS}
def epkX : Linear := {linear(plan['denominator'])}
def remainder : Linear := {linear(plan['remainder'])}
def ownedWrites : List Nat := {plan['writes']}
def kept : List Linear := [{', '.join(linear(lc) for lc in plan['kept'])}]
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(left)+','+linear(right)+'⟩' for left,right in plan['raw'].values())+f''']
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient rho [(0,1)] epkX remainder {q} {p} {a}
theorem coverage_checked : rawRows.all (fun actual =>
    (GroupRowCompletion.quotientRows [(0,1)] epkX remainder {q} {p} {a}).any (fun expected =>
      decide (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
        Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈
    GroupRowCompletion.quotientRows [(0,1)] epkX remainder {q} {p} {a},
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  GroupRowCompletion.extend_preserves rho [(0,1)] epkX remainder {q} {p} {a} column outside
theorem kept_checked : kept.all (fun terms => terms.all (fun term => decide (term.1 ∉ ownedWrites))) = true := by decide
theorem kept_preserved {{F : Type}} [Field F] (rho : Nat → F) :
    ∀ terms ∈ kept, eval (completeAssignment rho) terms = eval rho terms := by
  intro terms member
  apply eval_agrees
  intro term present
  exact preserves rho term.1 (of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp kept_checked) terms member)) term present))
theorem complete_rows {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) (legal : eval rho epkX ≠ 0) :
    Satisfies (completeAssignment rho) rawRows :=
  GroupRowCompletion.original_rows_complete rho [(0,1)] epkX remainder {q} {p} {a}
    (by decide) (by decide) (by decide) (by decide) legal rawRows {copy}
    (by decide) (by decide) linked coverage
theorem inverse_value {{F : Type}} [Field F] (rho : Nat → F) (one : rho 0 = 1) :
    completeAssignment rho {q} = (eval rho epkX)⁻¹ := by
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,one,add_zero]
  change GroupRowCompletion.extendQuotient rho [(0,1)] epkX remainder {q} {p} {a} {q} = _
  rw [GroupRowCompletion.quotient_value,unit,one_div]
theorem complete_inverse {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (legal : eval rho epkX ≠ 0) :
    Satisfies (completeAssignment rho) rawRows ∧
      completeAssignment rho {q} = (eval rho epkX)⁻¹ ∧
      (∀ column ∉ ownedWrites, completeAssignment rho column = rho column) :=
  ⟨complete_rows rho linked legal,inverse_value rho one,preserves rho⟩
'''
    for export in ('coverage_checked','coverage','preserves','kept_checked','kept_preserved','complete_rows','inverse_value','complete_inverse'):
        source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
