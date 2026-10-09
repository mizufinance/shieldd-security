"""One genuine blinding replay with a unique physical252 ORDER-1 chain.

The observer arms after canonical_bits; its metadata alone proves no endpoint.
This derivative reconstructs exact earlier compiler row pairs while forwarding
unchanged bytes to the full ordinary inspector. Native scalar zero is legal.
"""
from . import transfer_balance_blinding_fixed as ingress,transfer_balance_blinding_batch as batch
from . import transfer_balance_blinding_completion as local,transfer_arithmetic as arithmetic,transfer_relation as relation
from . import transfer_recovery_canonical as comparator,generate_transfer_fixed_spend as renderer
from .transfer_epk_fixed_canonical import _CandidateStream
from .transfer_balance_rows import canonical,source_index

SCHEMA='shieldd-transfer-balance-blinding-canonical-row-derivative-v1'


def boundary(checked):
    page=checked['chunks'][0];obj=page['metadata']
    bits=[page['expressions'][source_index(bit)] for bit in obj['bits']]
    value=page['expressions'][source_index(obj['blinding']['source'])]
    if (len(bits)!=252 or any(len(lc)!=1 or lc[0][1]!=1 for lc in bits) or len(value)!=1 or value[0][1]!=1):
        raise relation.RelationError('balance blinding exact scalar/252 singleton bit LCs')
    columns=[lc[0][0] for lc in bits]
    if len(set(columns)|{value[0][0]})!=253 or columns!=list(range(columns[0],columns[0]+252)):
        raise relation.RelationError('balance blinding actual contiguous distinct scalar/bit roles')
    if {0,1,2,6,obj['constant_copy'],value[0][0]}&set(columns):
        raise relation.RelationError('balance blinding bit writes alias protected input roles')
    return dict(checked=page,columns=columns,value=value[0][0],
        weighted=canonical((column,pow(2,index,relation.MODULUS)) for index,column in enumerate(columns)))


def _derive(checked,identity,raw,normalized,records):
    if (identity.get('relation_digest'),identity.get('domain_size'),identity.get('stored_rows'))!=(ingress.DIGEST,262144,200770):
        raise relation.RelationError('balance blinding canonical full production replay identity')
    selected=boundary(checked);certificate,used=comparator._chain(selected,raw,normalized)
    certificate.update(identity=identity,metadata_sha256=selected['checked']['metadata_sha256'],selected_rows=[records[i] for i in sorted(used)])
    return dict(schema=SCHEMA,parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        identity=identity,ordinary_replays=1,certificate=certificate,candidate_rows=len(records),
        candidate_terms=sum(len(a)+len(b) for a,b in raw.values()),
        scope='Unique real blinding ORDER-1 physical chain; scalar0 legal; native seed/fixed126/full balance OPEN')


def _fixed_projection(checked,combined):
    # The original fixed batch partition uses the exact same physical indices;
    # this projection adds no rows/roles and changes no qualifier flags.
    rows=batch._records(combined);descriptors=[];covered=set()
    for ordinal,page in enumerate(checked['chunks']):
        prefix=f'page.{ordinal}.';indices=set()
        for item in combined['templates']:
            if any(role.startswith(prefix) for role in item['roles']):indices.add(item['row'])
        for item in combined['products']:
            if item['role'].startswith(prefix):indices.update(item['rows'])
        if not indices<=rows.keys():raise relation.RelationError('balance blinding missing fixed selected row')
        extraction=dict(identity=combined['identity'],metadata_sha256=page['metadata_sha256'],include_canonical=False,
            selected_rows=[rows[i] for i in sorted(indices)])
        local.selection(page,extraction);covered.update(indices)
        descriptors.append(dict(ordinal=ordinal,window_start=16*ordinal,metadata_sha256=page['metadata_sha256'],rows=sorted(indices)))
    if covered!=rows.keys():raise relation.RelationError('balance blinding exact fixed projection coverage')
    return dict(identity=combined['identity'],parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        ordinary_replays=1,include_canonical=False,selected_rows=combined['selected_rows'],pages=descriptors)


def extract_rows(qualified_parent,raw_pages,expected_base,expected_blinding,stream):
    """Root-only ONE complete production replay, fixed126 plus canonical252."""
    checked=ingress.inspect_pages(qualified_parent,raw_pages,expected_base,expected_blinding);selected=boundary(checked)
    tap=_CandidateStream(stream,[selected],200692);required,products,squares=batch.requirements(checked)
    combined=arithmetic.extract_templates(tap,ingress.DIGEST,262144,200770,required,products,squares,label='balance-blinding-fixed-canonical')
    if not tap.eof or not tap.tail_checked:raise relation.RelationError('balance blinding full unchanged stream/EOF lifecycle')
    return dict(fixed=_fixed_projection(checked,combined),canonical=_derive(checked,combined['identity'],tap.raw,tap.normalized,tap.records),
        parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],ordinary_replays=1,
        scope='One full production replay; exact fixed and canonical derivatives; no assumed scalar endpoint or native group result')


def selection(checked,extracted):
    if (not isinstance(extracted,dict) or extracted.get('schema')!=SCHEMA or extracted.get('parent_sha256')!=checked['parent_sha256'] or
        extracted.get('raw_page_sha256')!=checked['raw_page_sha256'] or type(extracted.get('ordinary_replays'))is not int or extracted['ordinary_replays']!=1):
        raise relation.RelationError('balance blinding canonical retained parent/page/replay identity')
    selected=boundary(checked);certificate=extracted.get('certificate')
    if not isinstance(certificate,dict):raise relation.RelationError('balance blinding retained physical chain required')
    raw,normalized=arithmetic.normalize_selection(certificate,selected['checked']['metadata'],selected['checked']['metadata_sha256'])
    expected,used=comparator._chain(selected,raw,normalized)
    if (set(raw)!=used or comparator._json_value(extracted.get('identity'))!=comparator._json_value(certificate['identity']) or
        any(comparator._json_value(certificate.get(key))!=comparator._json_value(value) for key,value in expected.items())):
        raise relation.RelationError('balance blinding physical derivative certificate changed')
    return selected,certificate,expected,raw,normalized


def construction_plan(checked,extracted,*,readonly_lcs=()):
    selected,certificate,expected,raw,normalized=selection(checked,extracted)
    columns=selected['columns'];kept={0,1,2,6,200692,selected['value']};owned=set(columns);prior=set(kept)|owned
    for lc in readonly_lcs:
        if canonical(lc)!=tuple(lc) or any(type(c)is not int or not 0<=c<262144 for c,_ in lc):
            raise relation.RelationError('balance blinding canonical readonly LC schema')
        kept.update(c for c,_ in lc)
    if kept&owned:raise relation.RelationError('balance blinding canonical bits alias shared readonly roles')
    prior.update(kept);stages=[];rows=set();by_step={item['step']:item['rows'] for item in expected['products']}
    for index,step in enumerate(expected['steps']):
        if not index:continue
        product=arithmetic.product_certificate(step['before'],step['factor'],step['product'],normalized)
        stage=arithmetic.product_completion_certificate(step['before'],step['factor'],step['product'],product,normalized)
        if stage is None or product['rows']!=by_step[index]:raise relation.RelationError('balance blinding canonical exact original two-write product')
        writes={stage['output'],stage['auxiliary']}
        if writes&(owned|prior) or rows&set(stage['rows']):raise relation.RelationError('balance blinding canonical original freshness/ownership')
        owned.update(writes);rows.update(stage['rows']);prior.update(c for row in stage['rows'] for lc in raw[row] for c,_ in lc)
        stages.append(dict(stage,kind='product',step=index))
    templates={item['roles'][0]:item['row'] for item in expected['templates']}
    initial=[templates['boolean'+str(i)] for i in range(252)]+[templates['reconstruction']]
    boundary_rows=[templates['constant-copy'],templates['endpoint']]
    if set(raw)!=set(initial+boundary_rows)|rows:raise relation.RelationError('balance blinding canonical exact original coverage')
    return dict(value=selected['value'],bit_start=columns[0],width=252,stages=stages,chunks=[stages[i:i+16] for i in range(0,len(stages),16)],
        rows=sorted(raw),kept=sorted(kept),writes=sorted(owned),initial_rows=initial,boundary_rows=boundary_rows,
        endpoint=expected['steps'][-1]['after'],native_seed_contract='Same SDK blinding integer n with0<=n<Scalar.order; scalar LC=(n:F),constant/copy1. Zero is legal; no point/inverse/output premise.')


def generate(qualified_parent,raw_pages,expected_base,expected_blinding,extracted,*,readonly_lcs=()):
    checked=ingress.inspect_pages(qualified_parent,raw_pages,expected_base,expected_blinding)
    selected,certificate,expected,_,_=selection(checked,extracted);plan=construction_plan(checked,extracted,readonly_lcs=readonly_lcs)
    metadata=dict(constant_copy=200692,value=((selected['value'],1),),steps=[[s['before'],s['left'],{'native':f"{s['right']:064x}"},s['factor'],s['product'],s['after']] for s in expected['steps']])
    sound,_=comparator.generate_linear_checked(metadata,certificate);name='RuntimeBalanceBlindingCanonical'
    sound=sound.replace('RuntimeTransferRemainder',name).replace('actual_remainder_canonical','actual_blinding_canonical')
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
    sound=sound.replace(f'end ShielddSecurity.{name}',extra+f'end ShielddSecurity.{name}')
    # Neutral original constructor uses only n<order, so n=0 is admitted.
    order=name+'Order';complete=name+'Completion'
    return {name:sound,order:renderer.render_randomizer_order(plan,namespace=order),
        complete:renderer.render_randomizer_bit_completion(selected['checked'],plan,namespace=complete,order_namespace=order,sound_namespace=name)}
