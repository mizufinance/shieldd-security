"""Actual current two-note spend branch ingress and ordinary-row extraction.

No historical history/floor selector is accepted. Hash and Merkle outputs are
explicit source boundaries; this proves branch algebra, not their construction.
"""
import hashlib
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index

P = relation.MODULUS
SCOPE = 'two current Transfer spend source roles and branch LCs; hash/tree/range/native joins open'


def inspect_metadata(data, accepted_roles):
    if not isinstance(data, bytes) or len(data) > 2*1024*1024:
        raise relation.RelationError('note-spend metadata byte bound')
    if (not isinstance(accepted_roles, dict) or not isinstance(accepted_roles.get('metadata'), dict)
            or not isinstance(accepted_roles.get('observed'), dict)):
        raise relation.RelationError('accepted caller/spend roles required')
    try:
        obj = relation.record(data)
    except RecursionError as error:
        raise relation.RelationError('note-spend JSON nesting bound') from error
    keys = {'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
            'ordinary_full_ordered_rows_equal','repeated_observations_equal','spends','expressions','nodes'}
    if (set(obj) != keys or obj['schema'] != 'shieldd-transfer-note-spend-v1'
            or obj['family'] != 'transfer' or obj['scope'] != SCOPE):
        raise relation.RelationError('note-spend closed schema/scope mismatch')
    accepted = accepted_roles['metadata']
    domain = relation.natural(obj['domain_size']); count = relation.natural(obj['full_rows'])
    copy = relation.natural(obj['constant_copy'], domain)
    if (domain < 4 or domain & (domain-1) or not 0 < count <= domain or copy < 3
            or obj['ordinary_full_ordered_rows_equal'] is not True
            or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('note-spend shape/pending parity mismatch')
    if (obj['relation_digest'] != accepted.get('relation_digest')
            or any(relation.natural(accepted.get(k)) != obj[k]
                   for k in ('domain_size','full_rows','constant_copy'))):
        raise relation.RelationError('note-spend/caller relation identity mismatch')
    caller, authorization = accepted.get('caller'), accepted.get('spend')
    if not isinstance(caller, dict) or not isinstance(authorization, dict):
        raise relation.RelationError('accepted caller/spend roles missing')
    observed = _expressions(obj['expressions'], domain, copy, 512, 'note-spend')
    required = set()
    def value(v, *, native=False):
        if not isinstance(v, dict) or len(v) != 1:
            raise relation.RelationError('note-spend observed reference shape')
        if set(v) == {'native'} and native:
            encoded = v['native']
            if (not isinstance(encoded, str) or len(encoded) != 64
                    or any(c not in '0123456789abcdef' for c in encoded) or int(encoded,16) >= P):
                raise relation.RelationError('note-spend native encoding')
            return canonical([(0,int(encoded,16))])
        if set(v) != {'source'}:
            raise relation.RelationError('note-spend source reference required')
        index = source_index(v['source']); required.add(index)
        if index not in observed:
            raise relation.RelationError('note-spend expression coverage missing')
        return observed[index]
    def array(v, size):
        if not isinstance(v, list) or len(v) != size:
            raise relation.RelationError('note-spend role array shape')
        return tuple(value(x) for x in v)
    spends = obj['spends']
    if not isinstance(spends, list) or len(spends) != 2:
        raise relation.RelationError('note-spend requires exactly two ordered spends')
    fields = {'shared','note','commitment','position','amount_bits','position_bits',
              'real_nullifier','computed_anchor','nullifier','dummy','optional'}
    all_bits, note_witnesses = set(), set()
    parsed = []
    for slot, spend in enumerate(spends):
        if not isinstance(spend, dict) or set(spend) != fields:
            raise relation.RelationError('note-spend closed spend shape')
        shared = spend['shared']
        if not isinstance(shared, dict) or set(shared) != {'asset','address','nk','randomizer','anchor'}:
            raise relation.RelationError('note-spend closed shared shape')
        for name in ('asset','nk','randomizer','anchor'): value(shared[name])
        array(shared['address'],4)
        if (shared['asset'] != caller.get('asset') or shared['address'] != caller.get('address')
                or shared['nk'] != caller.get('effective_nk')
                or shared['randomizer'] != authorization.get('randomizer')):
            raise relation.RelationError('note-spend/caller shared role mismatch')
        if slot and shared != spends[0]['shared']:
            raise relation.RelationError('note-spend pair shared role mismatch')
        note = array(spend['note'],8)
        if spend['note'][2:7] != [shared['asset'],*shared['address']]:
            raise relation.RelationError('note-spend NOTE field role ordering mismatch')
        for v in [spend['note'][index] for index in (0,1,7)]+[spend['position'],spend['nullifier']]:
            if not isinstance(v,dict) or set(v) != {'source'}:
                raise relation.RelationError('note-spend note/position/nullifier witness required')
            handle = source_index(v['source'])
            if handle[0] != 1 or handle in note_witnesses:
                raise relation.RelationError('note-spend note witness alias/shape')
            note_witnesses.add(handle)
        current = dict(note=note, shared={name:value(shared[name]) for name in ('asset','nk','randomizer','anchor')})
        for name in ('commitment','position','real_nullifier','computed_anchor','nullifier'):
            current[name] = value(spend[name])
        for name, size in (('amount_bits',128),('position_bits',48)):
            bits = spend[name]
            if not isinstance(bits,list) or len(bits) != size:
                raise relation.RelationError('note-spend bit array shape')
            handles = tuple(source_index(bit) for bit in bits)
            if len(set(handles)) != size or any(h[0] != 1 or h in all_bits for h in handles):
                raise relation.RelationError('note-spend bit witnesses alias/shape')
            all_bits.update(handles); required.update(handles)
            if not set(handles) <= set(observed):
                raise relation.RelationError('note-spend bit expression coverage')
            current[name] = tuple(observed[h] for h in handles)
        current['dummy'] = value(spend['dummy'],native=(slot == 0))
        optional = spend['optional']
        if slot == 0:
            if optional is not None or spend['dummy'] != {'native':f'{0:064x}'}:
                raise relation.RelationError('note-spend required constructor policy mismatch')
        else:
            if (not isinstance(optional,dict) or set(optional) != {'domain','slot','seed','synthetic','selected','products'}
                    or type(optional['domain']) is not int or optional['domain'] != 22
                    or type(optional['slot']) is not int or optional['slot'] != 1):
                raise relation.RelationError('note-spend Transfer optional domain/slot policy mismatch')
            if source_index(spend['dummy']['source'])[0] != 1:
                raise relation.RelationError('note-spend optional dummy witness required')
            current.update({name:value(optional[name]) for name in ('seed','synthetic','selected')})
            for v in (spend['dummy'],optional['seed']):
                handle = source_index(v['source'])
                if handle[0] != 1 or handle in note_witnesses:
                    raise relation.RelationError('note-spend optional witness alias/shape')
                note_witnesses.add(handle)
            products = optional['products']
            if not isinstance(products,list) or len(products) != 3:
                raise relation.RelationError('note-spend requires three branch products')
            current['products'] = tuple(array(product,3) for product in products)
            bit, real, synthetic = current['dummy'], current['real_nullifier'], current['synthetic']
            expected = [(bit,combine(synthetic,real,-1)),
                        (combine(((0,1),),bit,-1),combine(current['computed_anchor'],current['shared']['anchor'],-1)),
                        (bit,note[1])]
            if any(product[:2] != wanted for product,wanted in zip(current['products'],expected)):
                raise relation.RelationError('note-spend branch product operand LC mismatch')
            if current['selected'] != combine(real,current['products'][0][2]):
                raise relation.RelationError('note-spend BoolVar.select source LC mismatch')
        parsed.append(current)
    if all_bits & note_witnesses or set(observed) != required:
        raise relation.RelationError('note-spend exact source coverage/bit alias mismatch')
    for handle, terms in accepted_roles['observed'].items():
        if handle in observed and terms != observed[handle]:
            raise relation.RelationError('note-spend/caller shared source LC mismatch')
    nodes = obj['nodes']
    if not isinstance(nodes,list) or len(nodes) != 3:
        raise relation.RelationError('note-spend exact product node count')
    table = {}; previous = -1
    for node in nodes:
        if not isinstance(node,dict) or set(node) != {'index','multiply','left','right'}:
            raise relation.RelationError('note-spend product node shape')
        index = relation.natural(node['index'])
        if index <= previous or node['multiply'] is not True:
            raise relation.RelationError('note-spend product node order/kind')
        previous = index; table[(2,index)] = (source_index(node['left']),source_index(node['right']))
    seen = set()
    for product in spends[1]['optional']['products']:
        left,right,output = (source_index(v['source']) for v in product)
        if output in seen or table.get(output) != (left,right):
            raise relation.RelationError('note-spend product source DAG correspondence mismatch')
        seen.add(output)
    return dict(metadata=obj,observed=observed,spends=parsed,
                metadata_sha256=hashlib.sha256(data).hexdigest())


def extract(data, stream, accepted_roles):
    checked = inspect_metadata(data, accepted_roles)
    obj = checked['metadata']; copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c,v) for c,v in lc)
    required = {(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    def assertion(role,left,right=()):
        equation = combine(left,right,-1)
        if not equation:
            raise relation.RelationError('note-spend assertion unexpectedly folded: '+role)
        required.setdefault((outline(equation),()),[]).append(role)
    first,second = checked['spends']
    assertion('required.nullifier',first['real_nullifier'],first['nullifier'])
    assertion('required.anchor',first['computed_anchor'],first['shared']['anchor'])
    bit = outline(second['dummy']); required[(bit,bit)] = ['optional.boolean']
    assertion('optional.selected',second['selected'],second['nullifier'])
    assertion('optional.anchor',second['products'][1][2])
    assertion('optional.amount',second['products'][2][2])
    products = [('optional.'+name,outline(combine(left,right,-1)),outline(combine(left,right)),outline(out),None)
                for name,(left,right,out) in zip(('selector','anchor','amount'),second['products'])]
    result = arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
                                          required,products,[],label='note-spend')
    result.update(metadata_sha256=checked['metadata_sha256'],scope='actual current two-note branch rows only; hash/tree/range/native joins open')
    return result


def certificates(data, extracted, accepted_roles):
    """Reaccept metadata and algebraically recheck persisted actual selections."""
    checked = inspect_metadata(data,accepted_roles)
    raw, rows = arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    first, second = checked['spends']; table = {row:index for index,row in rows.items()}
    def assertion(left,right=()):
        delta = combine(left,right,-1)
        for candidate,reverse in ((delta,False),(canonical((c,-v) for c,v in delta),True)):
            if (candidate,()) in table:return dict(row=table[(candidate,())],reverse=reverse)
        raise relation.RelationError('note-spend assertion selection missing')
    result = {'required.nullifier':assertion(first['real_nullifier'],first['nullifier']),
              'required.anchor':assertion(first['computed_anchor'],first['shared']['anchor']),
              'optional.selected':assertion(second['selected'],second['nullifier']),
              'optional.anchor':assertion(second['products'][1][2]),
              'optional.amount':assertion(second['products'][2][2])}
    if (second['dummy'],second['dummy']) not in table:
        raise relation.RelationError('note-spend boolean selection missing')
    result['optional.boolean'] = {'row':table[(second['dummy'],second['dummy'])]}
    for name,(left,right,out) in zip(('selector','anchor','amount'),second['products']):
        result['product.'+name] = dict(arithmetic.product_certificate(left,right,out,rows),left=left,right=right,output=out)
    used = {c['row'] for c in result.values() if 'row' in c}
    used.update(i for c in result.values() for i in c.get('rows',[]))
    used.update(i for i,row in raw.items() if row == (canonical([(0,1),(checked['metadata']['constant_copy'],-1)]),()))
    if used != set(raw):
        raise relation.RelationError('note-spend exact selected row coverage mismatch')
    return dict(checked=checked,rows=raw,certificates=result)


def generate(data, extracted, accepted_roles):
    """Generate only from rechecked ordinary rows, never from role labels alone."""
    from .generate_hash_round import linear, _signature_audits
    selection = certificates(data,extracted,accepted_roles)
    checked, rows, certs = selection['checked'],selection['rows'],selection['certificates']
    obj = checked['metadata']; first,second = checked['spends']; copy = obj['constant_copy']
    source = f'''import ShielddSecurity.Compiler
import ShielddSecurity.PermanentSpend
set_option maxHeartbeats 500000
namespace ShielddSecurity.RuntimeTransferNoteSpend
-- Full ordinary relation: {obj['relation_digest']}
-- Metadata SHA256 (byte identity only): {checked['metadata_sha256']}
-- Two current spend branches only; NOTE/NF/hash/tree/range/native joins OPEN.
def modulus : Nat := {P}
def originalRows : List Nat := {list(rows)}
def rawRows : List Row := [
'''
    source += ',\n'.join('  ⟨'+linear(a)+','+linear(b)+'⟩' for a,b in rows.values())+']\n'
    source += f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n'
    for prefix,spend in (('required',first),('optional',second)):
        for name,lc in (('Amount',spend['note'][1]),('Nullifier',spend['nullifier']),
                        ('RealNullifier',spend['real_nullifier']),('ComputedAnchor',spend['computed_anchor']),
                        ('Anchor',spend['shared']['anchor'])):
            source += f'def {prefix}{name} : Linear := {linear(lc)}\n'
    for name,lc in (('dummy',second['dummy']),('synthetic',second['synthetic']),('selected',second['selected'])):
        source += f'def {name} : Linear := {linear(lc)}\n'
    for name,(_,_,lc) in zip(('selector','anchor','amount'),second['products']):
        source += f'def {name}Product : Linear := {linear(lc)}\n'
    source += f'''theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
'''
    def asserted(role,left,right):
        reverse = certs[role]['reverse']
        a,b = (right,left) if reverse else (left,right)
        return f'(Compiler.checked_assertion_sound rho rows ({a}) ({b}) normalized (by decide))'+('.symm' if reverse else '')
    source += f'''theorem required_real {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho [] = 0 ∧ eval rho requiredNullifier = eval rho requiredRealNullifier ∧
      eval rho requiredComputedAnchor = eval rho requiredAnchor ∧
      PermanentSpend.BranchSpec (eval rho []) (eval rho requiredAmount) (eval rho requiredNullifier)
        (eval rho requiredRealNullifier) (eval rho []) (eval rho requiredComputedAnchor) (eval rho requiredAnchor) := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  exact PermanentSpend.required_assignment_real rho requiredAmount requiredNullifier requiredRealNullifier []
    requiredComputedAnchor requiredAnchor ({asserted('required.nullifier','requiredRealNullifier','requiredNullifier')}.symm)
    {asserted('required.anchor','requiredComputedAnchor','requiredAnchor')}
'''
    semantic = {'selector':('dummy','Compiler.subtract synthetic optionalRealNullifier'),
                'anchor':('Compiler.subtract [(0,1)] dummy','Compiler.subtract optionalComputedAnchor optionalAnchor'),
                'amount':('dummy','optionalAmount')}
    conclusions = {'selector':'eval rho dummy * (eval rho synthetic - eval rho optionalRealNullifier)',
                   'anchor':'(1 - eval rho dummy) * (eval rho optionalComputedAnchor - eval rho optionalAnchor)',
                   'amount':'eval rho dummy * eval rho optionalAmount'}
    for name in ('selector','anchor','amount'):
        cert = certs['product.'+name]
        # Source guards demand three materialized, non-square products. Other
        # lowering shapes are refused rather than guessed into this proof.
        if cert['kind'] != 'product':
            raise relation.RelationError('note-spend unsupported captured branch product lowering')
        left,right = semantic[name]
        if cert['swapped']: left,right = right,left
        source += f'''theorem {name}_product {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho {name}Product = {conclusions[name]} := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have multiplied := Compiler.checked_product_sound rho rows ({left}) ({right})
    {name}Product ({linear(cert['auxiliary'])}) four normalized (by decide) (by decide)
  simpa only [Compiler.eval_subtract, eval, Int.cast_one, one_mul, add_zero, one,
    mul_comm] using multiplied
'''
    source += f'''theorem optional_branch {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    PermanentSpend.BranchSpec (eval rho dummy) (eval rho optionalAmount) (eval rho optionalNullifier)
      (eval rho optionalRealNullifier) (eval rho synthetic)
      (eval rho optionalComputedAnchor) (eval rho optionalAnchor) := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have bit : Square (eval rho dummy) (eval rho dummy) :=
    Compiler.checked_row_sound rho rows ⟨dummy,dummy⟩ normalized (by decide)
  have selectedEq : eval rho selected = eval rho optionalNullifier :=
    {asserted('optional.selected','selected','optionalNullifier')}
  have selectedExpansion : eval rho selected = eval rho (optionalRealNullifier ++ selectorProduct) :=
    Compiler.canonical_equal rho selected (optionalRealNullifier ++ selectorProduct) (by decide)
  have selectedGate : eval rho optionalNullifier = eval rho dummy * eval rho synthetic +
      (1 - eval rho dummy) * eval rho optionalRealNullifier := by
    rw [← selectedEq, selectedExpansion, eval_append, selector_product rho one four satisfied]
    ring
  have anchorEq : eval rho anchorProduct = eval rho [] :=
    {asserted('optional.anchor','anchorProduct','[]')}
  have amountEq : eval rho amountProduct = eval rho [] :=
    {asserted('optional.amount','amountProduct','[]')}
  have anchorGate : (1 - eval rho dummy) *
      (eval rho optionalComputedAnchor - eval rho optionalAnchor) = 0 :=
    (anchor_product rho one four satisfied).symm.trans anchorEq
  have amountGate : eval rho dummy * eval rho optionalAmount = 0 :=
    (amount_product rho one four satisfied).symm.trans amountEq
  exact PermanentSpend.assignment_branch_sound rho dummy optionalAmount optionalNullifier
    optionalRealNullifier synthetic optionalComputedAnchor optionalAnchor bit selectedGate anchorGate amountGate

theorem both_spend_branches {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    PermanentSpend.BranchSpec (eval rho []) (eval rho requiredAmount) (eval rho requiredNullifier)
      (eval rho requiredRealNullifier) (eval rho []) (eval rho requiredComputedAnchor) (eval rho requiredAnchor) ∧
    PermanentSpend.BranchSpec (eval rho dummy) (eval rho optionalAmount) (eval rho optionalNullifier)
      (eval rho optionalRealNullifier) (eval rho synthetic)
      (eval rho optionalComputedAnchor) (eval rho optionalAnchor) :=
  ⟨(required_real rho satisfied).2.2.2, optional_branch rho one four satisfied⟩

#print axioms constantLink
#print axioms required_real
#print axioms selector_product
#print axioms anchor_product
#print axioms amount_product
#print axioms optional_branch
#print axioms both_spend_branches
end ShielddSecurity.RuntimeTransferNoteSpend
'''
    return _signature_audits(source)
