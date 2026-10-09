"""Bounded actual fixed-spend capture ingress; row and codec joins stay separate.

Accepted authorization roles are an explicit prior ingress result. Native table
values are checked by field arithmetic, never inferred from a source hash. The
product obligations returned here still require exact original row extraction.
"""
import hashlib

from . import transfer_relation as relation
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index
from .transfer_canonical_balance import comparison_obligations
from . import transfer_arithmetic as arithmetic

P = relation.MODULUS
D = -10240 * pow(10241, -1, P) % P
SCOPE = 'bounded actual ascending fixed-window arithmetic and LCs; canonical randomizer/native semantic joins open'
NATIVE_SOURCE_CONTRACT_FILES = (
    'crates/crypto/circuits/src/group.rs',
    'third_party/commonware/cryptography/src/bls12381/primitives/group.rs',
    'third_party/commonware/codec/src/codec.rs',
    'crates/crypto/primitives/src/generators.rs',
    'crates/crypto/primitives/src/lib.rs',
    'crates/crypto/primitives/src/encoding.rs',
)


def _native(value):
    if not isinstance(value, dict) or set(value) != {'native'}:
        raise relation.RelationError('fixed native table reference required')
    coefficient = value['native']
    if (not isinstance(coefficient, str) or len(coefficient) != 64 or
            any(c not in '0123456789abcdef' for c in coefficient) or int(coefficient, 16) >= P):
        raise relation.RelationError('noncanonical fixed native value')
    return int(coefficient, 16)


def _add(a, b):
    x, y = a; u, v = b
    product = D*x*u*y*v % P
    plus, minus = (1+product) % P, (1-product) % P
    if not plus or not minus:
        raise relation.RelationError('fixed native table zero denominator')
    return ((x*v+y*u)*pow(plus, -1, P) % P, (y*v+x*u)*pow(minus, -1, P) % P)


def inspect_metadata(data, accepted_roles):
    """Validate one <=16-window chunk and its exact accepted spend boundary.

    This deliberately emits pending product/quotient obligations rather than a
    theorem about their rows, canonical randomizer, or native byte codec.
    """
    if not isinstance(data, bytes) or len(data) > 4*1024*1024:
        raise relation.RelationError('fixed metadata size bound')
    if (not isinstance(accepted_roles, dict) or not isinstance(accepted_roles.get('metadata'), dict)
            or not isinstance(accepted_roles.get('observed'), dict)):
        raise relation.RelationError('accepted authorization roles required')
    try:
        obj = relation.record(data)
    except RecursionError as error:
        raise relation.RelationError('fixed JSON nesting bound') from error
    keys = {'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
            'ordinary_full_ordered_rows_equal','repeated_observations_equal','window_start',
            'window_count','total_windows','randomizer','generator','bits','output','canonical','windows','expressions'}
    if (set(obj) != keys or obj['schema'] != 'shieldd-transfer-fixed-spend-v1'
            or obj['family'] != 'transfer' or obj['scope'] != SCOPE):
        raise relation.RelationError('fixed closed schema/scope mismatch')
    accepted = accepted_roles['metadata']; spend = accepted.get('spend')
    if not isinstance(spend, dict):
        raise relation.RelationError('accepted spend roles absent')
    domain = relation.natural(obj['domain_size'])
    count = relation.natural(obj['full_rows'])
    copy = relation.natural(obj['constant_copy'], domain)
    if (domain < 4 or domain & (domain-1) or not 0 < count <= domain or copy < 3
            or obj['ordinary_full_ordered_rows_equal'] is not True
            or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('fixed relation shape/parity mismatch')
    if (obj['relation_digest'] != accepted.get('relation_digest') or
            any(relation.natural(accepted.get(key)) != obj[key]
                for key in ('domain_size','full_rows','constant_copy'))):
        raise relation.RelationError('fixed/authorization relation identity mismatch')
    start = relation.natural(obj['window_start'], 126)
    size = relation.natural(obj['window_count'], 17)
    if not 1 <= size <= 16 or start+size > 126 or type(obj['total_windows']) is not int or obj['total_windows'] != 126:
        raise relation.RelationError('fixed chunk bounds mismatch')
    bits = obj['bits']
    if not isinstance(bits, list) or len(bits) != 252:
        raise relation.RelationError('fixed bit shape mismatch')
    handles = tuple(source_index(bit) for bit in bits)
    if len(set(handles)) != 252 or any(tag != 1 for tag, _ in handles):
        raise relation.RelationError('fixed bits must be distinct witnesses')
    if (obj['randomizer'] != spend.get('randomizer') or obj['generator'] != spend.get('generator')
            or obj['output'] != spend.get('contribution') or bits != spend.get('bits')):
        raise relation.RelationError('fixed/authorization spend role mismatch')
    observed = _expressions(obj['expressions'], domain, copy, 4096, 'fixed')
    required = set(handles)
    def value(v):
        if not isinstance(v, dict) or len(v) != 1:
            raise relation.RelationError('malformed fixed observed reference')
        if set(v) == {'native'}:
            return canonical([(0, _native(v))])
        if set(v) != {'source'}:
            raise relation.RelationError('unknown fixed observed reference')
        index = source_index(v['source']); required.add(index)
        if index not in observed:
            raise relation.RelationError('missing fixed source LC')
        return observed[index]
    def array(values, length, convert=value):
        if not isinstance(values, list) or len(values) != length:
            raise relation.RelationError('wrong fixed array shape')
        return tuple(convert(v) for v in values)
    def point(values): return array(values, 2)
    randomizer = value(obj['randomizer']); output = point(obj['output'])
    comparator = obj['canonical']
    if not isinstance(comparator, dict) or set(comparator) != {'endpoint','steps'}:
        raise relation.RelationError('fixed canonical comparator shape')
    endpoint = source_index(comparator['endpoint'])
    endpoint_lc = value({'source':list(endpoint)})
    _, canonical_products = comparison_obligations(comparator['steps'],handles,endpoint,value)
    generator = array(obj['generator'], 2, _native)
    if (generator[1]**2-generator[0]**2-1-D*generator[0]**2*generator[1]**2) % P:
        raise relation.RelationError('fixed generator is off curve')
    weighted_base = generator
    for _ in range(start):
        twice = _add(weighted_base,weighted_base); weighted_base = _add(twice,twice)
    windows = obj['windows']
    if not isinstance(windows, list) or len(windows) != size:
        raise relation.RelationError('fixed window count mismatch')
    products = []; quotients = []; points = []; tables = []
    for offset, window in enumerate(windows):
        index = start+offset
        if not isinstance(window, dict) or set(window) != {'bits','table','points','arithmetic','quotient'}:
            raise relation.RelationError('fixed window closed shape mismatch')
        if (not isinstance(window['bits'], list) or len(window['bits']) != 2 or
                tuple(source_index(bit) for bit in window['bits']) != handles[2*index:2*index+2]):
            raise relation.RelationError('fixed little-endian window bit order mismatch')
        table = array(window['table'], 4, lambda pair: array(pair, 2, _native))
        base, twice, triple, next_base = table
        if twice != _add(base, base) or triple != _add(twice, base) or next_base != _add(twice, twice):
            raise relation.RelationError('fixed native 2/3/4 table recurrence mismatch')
        if offset and (tables[-1][3] != base):
            raise relation.RelationError('fixed native table chain mismatch')
        if offset == 0 and base != weighted_base:
            raise relation.RelationError('fixed native generator start mismatch')
        pts = array(window['points'], 3, point)
        before, selected, after = pts
        if offset and points[-1][2] != before:
            raise relation.RelationError('fixed accumulator LC chain mismatch')
        if index == 0 and before != ((), ((0,1),)):
            raise relation.RelationError('fixed accumulator identity start mismatch')
        if index == 125 and after != output:
            raise relation.RelationError('fixed output end mismatch')
        arithmetic = array(window['arithmetic'], 4)
        q = array(window['quotient'], 6)
        xx, yy, sum_product, xy_product = arithmetic
        expected = (combine(combine(sum_product,xx,-1),yy,-1), combine(yy,xx),
                    combine(((0,1),),canonical((c,v*D) for c,v in xy_product)),
                    combine(((0,1),),canonical((c,v*D) for c,v in xy_product),-1))
        if q[:4] != expected or q[4:] != after:
            raise relation.RelationError('fixed captured quotient formula/role mismatch')
        low, high = (observed[h] for h in handles[2*index:2*index+2])
        for axis in range(2):
            identity = axis
            lo = combine(((0,identity),) if identity else (), canonical((c,v*(base[axis]-identity)) for c,v in low))
            hi = combine(canonical([(0,twice[axis])]), canonical((c,v*(triple[axis]-twice[axis])) for c,v in low))
            products.append((f'window.{index}.select.{axis}', high, combine(hi,lo,-1), combine(selected[axis],lo,-1)))
        for name, left, right, result in (
                ('xx',before[0],selected[0],xx), ('yy',before[1],selected[1],yy),
                ('sum',combine(*before),combine(*selected),sum_product), ('xy',xx,yy,xy_product)):
            products.append((f'window.{index}.{name}',left,right,result))
        quotients.extend((f'window.{index}.quotient.{axis}',q[axis],q[axis+2],q[axis+4]) for axis in range(2))
        points.append(pts); tables.append(table)
    for role, left, right, result in products:
        for scalar, other in ((left,right),(right,left)):
            if not scalar or len(scalar) == 1 and scalar[0][0] == 0:
                factor = scalar[0][1] if scalar else 0
                if result != canonical((column, coefficient*factor) for column, coefficient in other):
                    raise relation.RelationError('fixed folded product LC mismatch: ' + role)
                break
    if set(observed) != required:
        raise relation.RelationError('fixed exact LC coverage mismatch')
    accepted_observed = accepted_roles['observed']
    for handle in set(observed) & set(accepted_observed):
        if observed[handle] != accepted_observed[handle]:
            raise relation.RelationError('fixed/authorization shared source LC mismatch')
    return dict(metadata=obj, observed=observed, points=points, tables=tables,
                products=products, quotients=quotients,
                canonical_products=canonical_products, canonical_endpoint=endpoint_lc,
                reconstruction=combine(canonical((3+handle[1],pow(2,i,P)) for i,handle in enumerate(handles)),randomizer,-1),
                metadata_sha256=hashlib.sha256(data).hexdigest(),
                scope='typed bounded fixed table/formula ingress only; actual rows/canonicality/native codec open')


def join_chunks(chunks):
    """Require exact all126 coverage and common source LCs before composition."""
    if not isinstance(chunks, list) or not 1 <= len(chunks) <= 126:
        raise relation.RelationError('fixed chunk collection bound')
    first = chunks[0]['metadata']; expected = 0; previous = None; observed = {}
    common = ('relation_digest','domain_size','full_rows','constant_copy','total_windows',
              'randomizer','generator','bits','output','canonical')
    for checked in chunks:
        obj = checked['metadata']
        if obj['window_start'] != expected or any(obj[key] != first[key] for key in common):
            raise relation.RelationError('fixed chunks omit/reorder/change boundary')
        if previous and (previous[0] != checked['points'][0][0] or previous[1] != checked['tables'][0][0]):
            raise relation.RelationError('fixed cross-chunk accumulator/table mismatch')
        for handle, lc in checked['observed'].items():
            if handle in observed and observed[handle] != lc:
                raise relation.RelationError('fixed cross-chunk shared LC mismatch')
            observed[handle] = lc
        expected += obj['window_count']
        previous = checked['points'][-1][2], checked['tables'][-1][3]
    if expected != 126:
        raise relation.RelationError('fixed chunks do not cover all126 windows')
    return dict(windows=126, chunks=len(chunks), observed=observed,
                scope='full bounded source/LC coverage only; row/kernel/native completion open')


def _requirements(checked, include_canonical):
    if type(include_canonical) is not bool:
        raise relation.RelationError('fixed canonical extraction flag')
    obj=checked['metadata']; copy=obj['constant_copy']
    def outlined(lc):return canonical((copy if c==0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    products=[];squares=[]
    def require(role,a,b=()):required.setdefault((outlined(a),outlined(b)),[]).append(role)
    def product(role,left,right,output):
        for scalar,other in ((left,right),(right,left)):
            if not scalar or len(scalar)==1 and scalar[0][0]==0:
                factor=scalar[0][1] if scalar else 0
                if output!=canonical((c,v*factor) for c,v in other):
                    raise relation.RelationError('fixed folded product mismatch')
                return
        if left==right:require(role+'.square',left,output)
        else:products.append((role,outlined(combine(left,right,-1)),outlined(combine(left,right)),outlined(output),None))
    for role,left,right,output in checked['products']:product(role,left,right,output)
    for role,numerator,denominator,quotient in checked['quotients']:
        folded=next(((scalar,other) for scalar,other in ((denominator,quotient),(quotient,denominator))
                     if not scalar or len(scalar)==1 and scalar[0][0]==0),None)
        if folded:
            scalar,other=folded;factor=scalar[0][1] if scalar else 0
            equation=combine(canonical((c,v*factor) for c,v in other),numerator,-1)
            if equation:require(role+'.assertion',equation)
        elif quotient==denominator:squares.append((role,outlined(quotient),outlined(numerator)))
        else:products.append((role,outlined(combine(quotient,denominator,-1)),
                              outlined(combine(quotient,denominator)),None,outlined(numerator)))
    start,size=obj['window_start'],obj['window_count']
    bit_indices=range(252) if include_canonical else range(2*start,2*(start+size))
    for i in bit_indices:
        bit=checked['observed'][source_index(obj['bits'][i])];require('boolean'+str(i),bit,bit)
    if include_canonical:
        for i,left,right,output in checked['canonical_products']:product('canonical.'+str(i),left,right,output)
        require('reconstruction',checked['reconstruction'])
        require('endpoint',combine(checked['canonical_endpoint'],((0,1),),-1))
    return required,products,squares


def extract_rows(data, accepted_roles, stream, *, include_canonical=True):
    """Reaccept bounded metadata and replay all ordinary rows before selecting."""
    checked=inspect_metadata(data,accepted_roles);obj=checked['metadata']
    required,products,squares=_requirements(checked,include_canonical)
    extracted=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
                                           required,products,squares,label='fixed')
    extracted.update(metadata_sha256=checked['metadata_sha256'],include_canonical=include_canonical,
                     scope='actual selected fixed/canonical rows only; source/kernel/native/full caller joins open')
    return extracted


def _selection(data, accepted_roles, extracted):
    checked=inspect_metadata(data,accepted_roles)
    raw,normalized=arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    include=extracted.get('include_canonical')
    required,_,_=_requirements(checked,include)
    copy=checked['metadata']['constant_copy']
    for (a,b),roles in required.items():
        if not any(row==(a,b) or not b and row==(canonical((c,-v) for c,v in a),b) for row in raw.values()):
            raise relation.RelationError('fixed selected actual template missing: '+roles[0])
    certificates={role:arithmetic.product_certificate(left,right,output,normalized)
                  for role,left,right,output in checked['products']}
    quotients={role:arithmetic.quotient_certificate(n,d,q,normalized) for role,n,d,q in checked['quotients']}
    canonical_certificates={}
    if include:
        for i,left,right,output in checked['canonical_products']:
            canonical_certificates[i]=arithmetic.product_certificate(left,right,output,normalized)
    return checked,raw,normalized,certificates,quotients,canonical_certificates


def generate_canonical(data, accepted_roles, extracted):
    """Reuse the bounded comparator generator for the private spend randomizer."""
    from .generate_transfer_canonical_balance import generate_checked
    checked,raw,normalized,_,_,canonical_certificates=_selection(data,accepted_roles,extracted)
    if extracted['include_canonical'] is not True:
        raise relation.RelationError('fixed canonical rows were not extracted')
    obj=checked['metadata'];spend=obj['randomizer']
    if set(spend)!={'source'} or source_index(spend['source'])[0]!=1:
        raise relation.RelationError('fixed randomizer witness required')
    # The existing renderer takes the actual step handles and exact selected
    # rows. This adapter changes names/scope, never invents a comparator DAG.
    m=dict(constant_copy=obj['constant_copy'],value=spend['source'],bits=obj['bits'],
           endpoint=obj['canonical']['endpoint'],steps=obj['canonical']['steps'],expressions=obj['expressions'])
    required=({'constant-copy','reconstruction','endpoint'}|{'boolean'+str(i) for i in range(252)})
    targets={role:target for target,names in _requirements(checked,True)[0].items()
             for role in names if role in required}
    roles={role:next(index for index,row in raw.items() if row==target or
                    not target[1] and row==(canonical_neg(target[0]),target[1])) for role,target in targets.items()}
    if set(roles)!=required:raise relation.RelationError('fixed canonical selected role coverage')
    template_rows={index:row for index,row in raw.items()}
    for role,index in roles.items():
        index=relation.natural(index,obj['full_rows'])
        target=targets[role]
        if template_rows.get(index) not in (target,(canonical_neg(target[0]),target[1])):
            raise relation.RelationError('fixed canonical selected role semantics')
    entries=[]
    for i,certificate in canonical_certificates.items():
        if certificate['kind']!='product' or certificate.get('swapped'):
            raise relation.RelationError('fixed canonical renderer requires original oriented product pairs')
        entries.append(dict(step=i,rows=certificate['rows']))
    canonical_extraction=dict(selected_rows=extracted['selected_rows'],
                              templates=[dict(roles=[role],row=index) for role,index in roles.items()],products=entries)
    source,_=generate_checked(m,canonical_extraction,private_remainder=True)
    source=source.replace('RuntimeTransferRemainder','RuntimeTransferRandomizer').replace(
        'actual_remainder_canonical','actual_randomizer_canonical')
    # Retain the exact decoded scalar for composition with the same fixed bits,
    # rather than lose its identity behind an existential natural number.
    extra='''def bits : List Linear := steps.map StepData.left
noncomputable def decodedBits {F : Type} [Field F] (rho : Nat → F) : List Bool :=
  ScalarBits.decodeBits rho bits
theorem actual_randomizer_bits {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho originalRows) :
    binary (decodedBits rho) < Scalar.order ∧
      (binary (decodedBits rho) : F) = eval rho privateValue := by
  have unoutlined : Satisfies rho rows :=
    unoutline_rows_sound rho copyColumn originalRows satisfied checked_copy
  have bound := ScalarComparisonBounds.checked_remainder_bound rho one four rows unoutlined
    steps checked_bits checked_chain checked_endpoint checked_maximum
  have decoded := ScalarBits.decoded_bits_value rho rows unoutlined bits checked_bits
  have rebuilt := ScalarComparisonBounds.checked_equality rho rows unoutlined
    (ScalarBits.bitLinear bits) privateValue checked_reconstruction
  exact ⟨bound,decoded.symm.trans rebuilt⟩
set_option pp.all true in
#check @actual_randomizer_bits
#print axioms actual_randomizer_bits
'''
    return source.replace('end ShielddSecurity.RuntimeTransferRandomizer',
                          extra+'end ShielddSecurity.RuntimeTransferRandomizer')


def canonical_neg(lc):return canonical((column,-value) for column,value in lc)


def randomizer_completion_plan(data, accepted_roles, extracted):
    """Plan the real bit block and comparator products without row truth inputs.

    Bits are constructed before any consumer. Comparator carry/aux pivots are
    owned only when exact actual rows and prior-support checks admit them.
    Endpoint legality follows separately from canonical integer comparison;
    this returned recipe does not assume or qualify that endpoint result.
    """
    checked,raw,normalized,_,_,certificates=_selection(data,accepted_roles,extracted)
    if extracted['include_canonical'] is not True:
        raise relation.RelationError('randomizer completion needs canonical row extraction')
    obj=checked['metadata'];handles=[source_index(bit) for bit in obj['bits']]
    start=3+handles[0][1]
    if handles!=[(1,handles[0][1]+i) for i in range(252)]:
        raise relation.RelationError('randomizer completion requires exact consecutive captured bits')
    scalar=source_index(obj['randomizer']['source'])
    if scalar[0]!=1:raise relation.RelationError('randomizer completion requires captured scalar witness')
    scalar_column=3+scalar[1];bit_writes=set(range(start,start+252))
    kept={0,1,2,obj['constant_copy'],scalar_column}
    bit_handles=set(handles)
    for handle,lc in accepted_roles['observed'].items():
        if handle not in bit_handles:kept.update(c for c,_ in lc)
    if kept&bit_writes:raise relation.RelationError('randomizer bits alias an externally owned role')
    owned=set(bit_writes);prior=set(bit_writes);stages=[];covered=set()
    for index,left,right,output in checked['canonical_products']:
        c=arithmetic.product_completion_certificate(left,right,output,certificates[index],normalized)
        if c is None:raise relation.RelationError('randomizer comparator unsupported product shape: '+str(index))
        writes={c['output'],c['auxiliary']}
        if writes&(kept|owned|prior):
            raise relation.RelationError('randomizer comparator writes alias kept/prior support: '+str(index))
        if covered&set(c['rows']):raise relation.RelationError('randomizer comparator original rows overlap')
        owned.update(writes);covered.update(c['rows'])
        for row in c['rows']:
            for side in normalized[row]:prior.update(column for column,_ in side)
        stages.append(dict(step=index,**c))
    required={'constant-copy','reconstruction','endpoint'}|{'boolean'+str(i) for i in range(252)}
    tails={}
    for target,names in _requirements(checked,True)[0].items():
        for name in set(names)&required:
            index=next((i for i,row in raw.items() if row==target or not target[1] and
                       row==(canonical_neg(target[0]),target[1])),None)
            if index is None:raise relation.RelationError('randomizer completion exact role row missing: '+name)
            tails[name]=index
    if set(tails)!=required:raise relation.RelationError('randomizer completion role coverage changed')
    if len(stages)!=251:raise relation.RelationError('randomizer completion comparator stage coverage')
    rows=sorted(covered|set(tails.values()))
    chunks=[stages[i:i+16] for i in range(0,len(stages),16)]
    return dict(value=scalar_column,bit_start=start,width=252,stages=stages,chunks=chunks,
                rows=rows,role_rows=tails,kept=sorted(kept),writes=sorted(owned),
                scope='exact bit/comparator construction recipe only; symbolic endpoint/row/native/caller proofs pending')


def fixed_completion_plan(data, accepted_roles, extracted):
    """Sequence actual bounded window writes and cover every retained row.

    Folded identity products contribute no invented rows. The captured first
    window's denominator-one quotients contribute their sole fresh linear
    pivot. Later quotients retain all three original lowered rows and writes.
    This is an ownership recipe; group denominator legality and whole-loop
    same-assignment/source/native proofs remain separate obligations.
    """
    checked,raw,normalized,products,quotients,_=_selection(data,accepted_roles,extracted)
    obj=checked['metadata'];start=obj['window_start'];count=obj['window_count']
    output_handles={source_index(ref['source']) for ref in obj['output']}
    kept={0,1,2,obj['constant_copy']}
    for handle,lc in accepted_roles['observed'].items():
        if handle not in output_handles:kept.update(column for column,_ in lc)
    # The previous chunk's actual accumulator is an input, not a fresh pivot.
    for lc in checked['points'][0][0]:kept.update(column for column,_ in lc)
    prior=set();covered=set();owned=set();initial_rows=set()
    if extracted['include_canonical']:
        initial_rows.update(randomizer_completion_plan(data,accepted_roles,extracted)['rows'])
    required={'constant-copy'}|{'boolean'+str(i) for i in range(2*start,2*(start+count))}
    for target,names in _requirements(checked,extracted['include_canonical'])[0].items():
        if set(names)&required:
            index=next((i for i,row in raw.items() if row==target or not target[1] and
                        row==(canonical_neg(target[0]),target[1])),None)
            if index is None:raise relation.RelationError('fixed completion initial row missing')
            initial_rows.add(index)
    for index in initial_rows:
        for side in normalized[index]:prior.update(column for column,_ in side)
    covered.update(initial_rows)
    product_inputs={role:(left,right,output) for role,left,right,output in checked['products']}
    windows=[]
    for index in range(start,start+count):
        stages=[];folded=[];folded_quotients=[]
        for suffix in ('select.0','select.1','xx','yy','sum','xy'):
            role=f'window.{index}.{suffix}';certificate=products[role]
            if certificate['kind'].startswith('folded_'):
                if certificate['rows']:raise relation.RelationError('fixed folded product has invented rows')
                folded.append(role);continue
            c=arithmetic.product_completion_certificate(*product_inputs[role],certificate,normalized)
            if c is None:raise relation.RelationError('fixed completion unsupported product shape: '+role)
            stages.append(dict(kind='product',role=role,**c))
        for axis in range(2):
            role=f'window.{index}.quotient.{axis}';certificate=quotients[role]
            if certificate['kind']=='folded':
                if (not certificate['rows'] and certificate['denominator']==((0,1),)
                        and certificate['quotient']==certificate['numerator']):
                    folded_quotients.append(role);continue
                c=arithmetic.folded_quotient_completion_certificate(certificate,normalized);kind='linear'
            else:c=arithmetic.completion_certificate(certificate,normalized);kind='quotient'
            if c is None:raise relation.RelationError('fixed completion unsupported quotient shape: '+role)
            stages.append(dict(kind=kind,role=role,**c))
        for stage in stages:
            writes=({stage['output']} if stage['kind']=='linear' else
                    {stage['output'],stage['auxiliary']} if stage['kind']=='product' else
                    {stage['quotient'],stage['product'],stage['auxiliary']})
            if writes&(kept|owned|prior):
                raise relation.RelationError('fixed completion writes alias kept/prior support: '+stage['role'])
            if covered&set(stage['rows']):raise relation.RelationError('fixed completion original row ownership overlaps')
            owned.update(writes);covered.update(stage['rows'])
            for row in stage['rows']:
                for side in normalized[row]:prior.update(column for column,_ in side)
        windows.append(dict(index=index,stages=stages,folded_products=folded,folded_quotients=folded_quotients))
    if covered!=set(raw):raise relation.RelationError('fixed completion does not cover every selected original row')
    return dict(window_start=start,window_count=count,windows=windows,kept=sorted(kept),writes=sorted(owned),
                initial_rows=sorted(initial_rows),original_rows=sorted(raw),
                scope='exact bounded window ownership recipe; legal denominators/whole assignment/native/caller proofs pending')


def fixed_completion_join(captures, accepted_roles, extractions):
    """Exact all126 construction ownership, including previous chunk supports.

    The finite recipe is not a Lean proof or capture qualification. It ensures
    the maintained whole-loop generator cannot silently discard earlier rows,
    rename shared inputs, or overwrite caller/randomizer/previous pivots.
    """
    if (not isinstance(captures,list) or not isinstance(extractions,list)
            or len(captures)!=len(extractions) or not 1<=len(captures)<=8):
        raise relation.RelationError('fixed completion join requires matching bounded chunks')
    selections=[_selection(data,accepted_roles,extracted)
                for data,extracted in zip(captures,extractions)]
    checked=[selection[0] for selection in selections]
    join_chunks(checked)
    randomizer=randomizer_completion_plan(captures[0],accepted_roles,extractions[0])
    plans=[fixed_completion_plan(data,accepted_roles,extracted)
           for data,extracted in zip(captures,extractions)]
    kept=set(plans[0]['kept']);owned=set(randomizer['writes'])
    raw={};normalized={}
    for _,rows,normal,*_ in selections:
        for index,row in rows.items():
            if index in raw and raw[index]!=row:
                raise relation.RelationError('fixed completion cross-chunk original row mismatch')
            raw[index]=row;normalized[index]=normal[index]
    prior_rows=set(randomizer['rows']);prior=set()
    for row in prior_rows:
        for side in normalized[row]:prior.update(column for column,_ in side)
    programs=[]
    for plan,selection in zip(plans,selections):
        for window in plan['windows']:
            index=window['index'];offset=index-plan['window_start'];writes=set();rows=set()
            before,_,after=selection[0]['points'][offset]
            support_before=sorted(prior)
            for stage in window['stages']:
                current=({stage['output']} if stage['kind']=='linear' else
                         {stage['output'],stage['auxiliary']} if stage['kind']=='product' else
                         {stage['quotient'],stage['product'],stage['auxiliary']})
                if current&(kept|owned|prior):
                    raise relation.RelationError('fixed global completion writes alias earlier chunk/caller support: '+stage['role'])
                if rows.intersection(stage['rows']) or prior_rows.intersection(stage['rows']):
                    raise relation.RelationError('fixed global completion original row ownership overlaps')
                owned.update(current);writes.update(current);rows.update(stage['rows'])
                for row in stage['rows']:
                    for side in normalized[row]:prior.update(column for column,_ in side)
            prior_rows.update(rows)
            programs.append(dict(index=index,input=before,output=after,
                stages=window['stages'],writes=sorted(writes),rows=sorted(rows),
                prior_support=support_before))
    if len(programs)!=126 or [program['index'] for program in programs]!=list(range(126)):
        raise relation.RelationError('fixed global completion program coverage')
    if prior_rows!=set(raw):
        raise relation.RelationError('fixed global completion misses selected original rows')
    return dict(programs=programs,kept=sorted(kept),initial_rows=randomizer['rows'],
                initial_writes=randomizer['writes'],rows=sorted(raw),
                writes=sorted(column for program in programs for column in program['writes']),
                constant_copy=checked[0]['metadata']['constant_copy'],
                scope='exact126 construction ownership recipe; symbolic/kernel/native/caller composition pending')


def _completion_frames(programs, raw, initial_rows, randomizer, copy):
    """Strict numeric certificates for the actual separate allocation cursors.

    This is only support/freshness data. The companion symbolic lemma derives
    prior-row freshness from local certificates; it does not check satisfaction
    or assume any resulting group/scalar meaning.
    """
    high_start=min(column for stage in randomizer['stages']
                   for column in (stage['output'],stage['auxiliary']))
    frames=[];before=None
    def covers(column,frame):
        return column<frame['low'] or high_start<=column<frame['high'] or column==copy
    for program in programs:
        low_writes=sorted(stage['output'] if stage['kind']=='linear' else stage['quotient']
                         for stage in program['stages'] if stage['kind'] in ('linear','quotient'))
        high_writes=sorted(column for stage in program['stages']
            for column in ((stage['output'],stage['auxiliary']) if stage['kind']=='product' else
                           (stage['product'],stage['auxiliary']) if stage['kind']=='quotient' else ()))
        if (len(low_writes)!=2 or low_writes[1]!=low_writes[0]+1 or not high_writes
                or len(set(high_writes))!=len(high_writes)):
            raise relation.RelationError('fixed support bounds require two consecutive witness pivots and fresh compiler pivots')
        current=dict(low=low_writes[0],high=min(high_writes))
        if before is None:
            before=current
            initial_support={column for index in initial_rows for side in raw[index] for column,_ in side}
            if any(not covers(column,before) for column in initial_support):
                raise relation.RelationError('fixed initial support does not fit allocation bounds')
        elif before!=current:
            raise relation.RelationError('fixed support allocation cursors are not contiguous')
        after=dict(low=low_writes[-1]+1,high=max(high_writes)+1)
        if sorted(program['writes'])!=sorted(low_writes+high_writes):
            raise relation.RelationError('fixed support bounds omit an owned write')
        if any(covers(column,before) for column in program['writes']):
            raise relation.RelationError('fixed owned write intersects prior support bounds')
        # W.rawRows includes the two protected Boolean rows and the copy link.
        # They already belong to initial_rows; include their support explicitly.
        local_support={column for index in program['rows'] for side in raw[index] for column,_ in side}
        local_support.update(program.get('bit_support',()))
        local_support.update((0,copy))
        if any(not covers(column,after) for column in local_support):
            raise relation.RelationError('fixed local row support exceeds next allocation bounds')
        frames.append(dict(index=program['index'],before=before,after=after,
                           rows=program['rows'],support=sorted(local_support),writes=program['writes']))
        before=after
    return dict(high_start=high_start,constant_copy=copy,initial=frames[0]['before'],
                frames=frames,scope='local support-bound certificates; symbolic freshness/kernel/whole construction pending')


def fixed_completion_bounds(data, accepted_roles, extracted):
    """Bounded first-chunk support certificates from exact retained rows."""
    plan=fixed_completion_plan(data,accepted_roles,extracted)
    if plan['window_start']!=0:
        raise relation.RelationError('fixed support bounds require initial canonical chunk')
    checked,raw,*_=_selection(data,accepted_roles,extracted)
    randomizer=randomizer_completion_plan(data,accepted_roles,extracted)
    programs=[]
    for window in plan['windows']:
        stages=window['stages'];writes=set();rows=set()
        for stage in stages:
            writes.update([stage['output']] if stage['kind']=='linear' else
                          [stage['output'],stage['auxiliary']] if stage['kind']=='product' else
                          [stage['quotient'],stage['product'],stage['auxiliary']])
            rows.update(stage['rows'])
        index=window['index']
        bits=checked['metadata']['bits'][2*index:2*index+2]
        support=[column for bit in bits for column,_ in checked['observed'][source_index(bit)]]
        programs.append(dict(index=index,stages=stages,writes=sorted(writes),rows=sorted(rows),bit_support=support))
    return _completion_frames(programs,raw,randomizer['rows'],randomizer,checked['metadata']['constant_copy'])


def fixed_completion_bounds_join(captures, accepted_roles, extractions):
    """All126 support certificates; ordinary ownership/join remains mandatory."""
    plan=fixed_completion_join(captures,accepted_roles,extractions)
    selections=[_selection(data,accepted_roles,extracted) for data,extracted in zip(captures,extractions)]
    raw={index:row for selection in selections for index,row in selection[1].items()}
    randomizer=randomizer_completion_plan(captures[0],accepted_roles,extractions[0])
    for program in plan['programs']:
        bits=selections[0][0]['metadata']['bits'][2*program['index']:2*program['index']+2]
        program['bit_support']=[column for bit in bits
            for column,_ in selections[0][0]['observed'][source_index(bit)]]
    return _completion_frames(plan['programs'],raw,plan['initial_rows'],randomizer,plan['constant_copy'])
