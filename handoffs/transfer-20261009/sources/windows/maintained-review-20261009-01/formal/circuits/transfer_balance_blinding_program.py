"""Constructive fixed126 composition behind genuine VALUE_BLINDING ingress.

No EPK or spend metadata is converted. Neutral maintained renderers consume
the exact checked LCs, physical rows, canonical plan and ownership frames.
Zero blinding is admitted; no inverse or nonidentity premise is introduced.
"""
from . import transfer_balance_blinding_fixed as ingress, transfer_balance_blinding_batch as batch
from . import transfer_balance_blinding_completion as local, transfer_balance_blinding_canonical as scalar
from . import transfer_fixed_spend as fixed, transfer_arithmetic as arithmetic, transfer_relation as relation
from . import generate_transfer_fixed_spend as renderer
from .transfer_balance_rows import source_index
from .generate_hash_round import _signature_audits


def plan(qualified_parent, raw_pages, expected_base, expected_blinding, extracted, readonly_lcs=()):
    if (not isinstance(extracted, dict) or set(extracted) != {'fixed','canonical','parent_sha256',
            'raw_page_sha256','ordinary_replays','scope'} or
            type(extracted['ordinary_replays']) is not int or extracted['ordinary_replays'] != 1):
        raise relation.RelationError('blinding126 one genuine fixed/canonical original row union required')
    checked = ingress.inspect_pages(qualified_parent, raw_pages, expected_base, expected_blinding)
    if (extracted['parent_sha256'] != checked['parent_sha256'] or
            extracted['raw_page_sha256'] != checked['raw_page_sha256'] or
            extracted['fixed']['identity'] != extracted['canonical']['identity']):
        raise relation.RelationError('blinding126 exact parent/raw/full original identity')
    canonical = scalar.construction_plan(checked, extracted['canonical'], readonly_lcs=readonly_lcs)
    raw = scalar.selection(checked, extracted['canonical'])[3]
    initial = set(canonical['rows'])
    canonical_writes = set(canonical['writes'])
    owned = set(); prior_rows = set(); prior_support = set(); all_rows = set(); programs = []
    kept = set(canonical['kept']) | set(range(canonical['bit_start'], canonical['bit_start']+252))
    protected = set(kept)
    selections = []; local_plans = []
    for ordinal, page in enumerate(checked['chunks']):
        selection = batch.page_selection(checked, extracted['fixed'], ordinal)
        construction = local.completion_plan(page, selection, readonly_lcs=readonly_lcs)
        current = arithmetic.normalize_selection(selection, page['metadata'], page['metadata_sha256'])[0]
        for index, row in current.items():
            if index in raw and raw[index] != row:
                raise relation.RelationError('blinding126 canonical/fixed original row differs')
            raw[index] = row
        selections.append(selection); local_plans.append(construction)
        kept.update(construction['kept']); all_rows.update(current)
        for window in construction['windows']:
            rows = set(); writes = set()
            for stage in window['stages']:
                columns = ({stage['output']} if stage['kind']=='linear' else
                           {stage['output'],stage['auxiliary']} if stage['kind']=='product' else
                           {stage['quotient'],stage['product'],stage['auxiliary']})
                if columns & (owned | canonical_writes | protected | prior_support):
                    raise relation.RelationError('blinding126 writes overlap canonical/shared/prior support')
                if set(stage['rows']) & (rows | prior_rows | initial):
                    raise relation.RelationError('blinding126 exact original owned row overlap')
                writes.update(columns); owned.update(columns); rows.update(stage['rows'])
                prior_support.update(c for i in stage['rows'] for side in raw[i] for c,_ in side)
            prior_rows.update(rows)
            index = window['index']; offset = index-page['metadata']['window_start']
            before, _, after = page['points'][offset]
            if index != len(programs) or programs and programs[-1]['output'] != before:
                raise relation.RelationError('blinding126 exact ordered source endpoint continuity')
            bit_support = []
            for axis, source in enumerate(page['metadata']['bits'][2*index:2*index+2]):
                terms = page['expressions'][source_index(source)]
                column = canonical['bit_start']+2*index+axis
                if terms != ((column,1),):
                    raise relation.RelationError('blinding126 exact canonical singleton bit association')
                bit_support.append(column)
            programs.append(dict(index=index,input=before,output=after,stages=window['stages'],
                writes=sorted(writes),rows=sorted(rows),bit_support=bit_support,
                folded_products=window['folded_products'],folded_quotients=window['folded_quotients']))
    if len(programs) != 126 or programs[0]['input'] != ((),((0,1),)):
        raise relation.RelationError('blinding126 full identity-to-endpoint construction required')
    if all_rows != {row['row'] for row in extracted['fixed']['selected_rows']} or all_rows-initial != prior_rows:
        raise relation.RelationError('blinding126 full original fixed row coverage')
    if any(c in owned for i in initial for side in raw[i] for c,_ in side):
        raise relation.RelationError('blinding126 later writes destroy canonical original rows')
    kept -= owned
    if not protected <= kept:
        raise relation.RelationError('blinding126 shared protected roles missing')
    bounds = fixed._completion_frames(programs,raw,initial,canonical,200692)
    loop = dict(programs=programs,initial_rows=sorted(initial),rows=sorted(all_rows),
                kept=sorted(kept),writes=sorted(owned))
    return dict(checked=checked,selections=selections,local_plans=local_plans,canonical=canonical,
                loop=loop,bounds=bounds,identity=extracted['fixed']['identity'],
                parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
                scope='Exact canonical252/fixed126 owned-row composition; scalar0 legal; native parameter/source/curve/whole balance frame joins open')


def _description(source):
    # Replace only the neutral renderer's explanatory SpendAuth provenance.
    # The theorem's standardGenerator/model contracts remain explicit.
    start = source.find('-- Native/source boundary at shieldd.lock')
    end = source.find('def modulus : Nat :=', start)
    if start < 0 or end < start:
        raise relation.RelationError('blinding126 neutral native description anchor drift')
    description = '''-- Genuine VALUE_BLINDING source boundary at shieldd.lock844389ee069e1fb2e576708842d0b389b4d9a44a.
-- balance.rs canonical_bits(blinding)/multiply_fixed; map.rs Generators.blinding
-- binds native_point(SDK VALUE_BLINDING). Exact native coordinate codec/reader,
-- standard generator/model and caller blinding object association remain contracts.
-- Canonical scalarzero and its identity contribution are legal; no x inverse.
'''
    return (source[:start]+description+source[end:]).replace('spendAuthRole','valueBlindingRole').replace('spendAuth','valueBlinding')


def frame_source(start):
    relation.natural(start,262144)
    if not 3 <= start < 262144-252:
        raise relation.RelationError('blinding126 exact canonical bit footprint required')
    C='ShielddSecurity.RuntimeBalanceBlindingFixedCompletion'
    O='ShielddSecurity.RuntimeBalanceBlindingCanonicalOrder'
    R='ShielddSecurity.RuntimeBalanceBlindingCanonicalCompletion'
    source=f'''import {C}
import ShielddSecurity.PoseidonCompletion
namespace ShielddSecurity.RuntimeBalanceBlindingFixedFrame
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
def ownedWrites (n : Nat) : List Nat := List.range' {start} 252 ++
  PoseidonCompletion.writes {O}.allStages ++
    ({C}.programs n).flatMap (fun program => program.stages.flatMap GroupCircuitCompletion.Step.writes)
theorem outside_column {{F : Type}} [Field F] (base : Nat → F) (n column : Nat)
    (outside : column ∉ ownedWrites n) : {C}.construct base n column = base column := by
  have absentBits : column ∉ List.range' {start} 252 := by
    intro member
    exact outside (List.mem_append_left _ (List.mem_append_left _ member))
  have absentProducts : column ∉ PoseidonCompletion.writes {O}.allStages := by
    intro member
    exact outside (List.mem_append_left _ (List.mem_append_right _ member))
  have preserved : ∀ program ∈ {C}.programs n, GroupFixedCircuitCompletion.Protected [column] program := by
    intro program member stage present current kept written
    have same : current = column := List.mem_singleton.mp kept
    subst current
    exact outside (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨program,member,List.mem_flatMap.mpr ⟨stage,present,written⟩⟩))
  have loops := GroupFixedCircuitCompletion.run_preserves
    ({R}.construct base n) ({C}.programs n) [column] preserved column (List.mem_singleton_self column)
  have products := PoseidonCompletion.run_outside (writeBits base {start} (encodeBits 252 n))
    {O}.allStages column absentProducts
  have rangeOutside : column < {start} ∨ {start}+252 ≤ column := by
    by_contra denied
    have inside : {start} ≤ column ∧ column < {start}+252 := by omega
    exact absentBits (List.mem_range'_1.mpr inside)
  have bitValue := writeBits_preserves base {start} (encodeBits 252 n) column
    (by simpa only [encodeBits_length] using rangeOutside)
  exact loops.trans (products.trans bitValue)
theorem outside_eval {{F : Type}} [Field F] (base : Nat → F) (n : Nat) (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 ∉ ownedWrites n) :
    eval ({C}.construct base n) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside_column base n term.1 (outside term member)
theorem outside_row {{F : Type}} [Field F] (base : Nat → F) (n : Nat) (row : Row)
    (outside : ∀ term ∈ row.a ++ row.b, term.1 ∉ ownedWrites n) :
    eval ({C}.construct base n) row.a = eval base row.a ∧
      eval ({C}.construct base n) row.b = eval base row.b :=
  ⟨outside_eval base n row.a (by intro term member; exact outside term (List.mem_append_left _ member)),
   outside_eval base n row.b (by intro term member; exact outside term (List.mem_append_right _ member))⟩
#print axioms outside_column
#print axioms outside_eval
#print axioms outside_row
end ShielddSecurity.RuntimeBalanceBlindingFixedFrame
'''
    return _signature_audits(source)


def native_scalar_source():
    """Derive the H endpoint from its OWN constructed canonical/loop rows.

    Zero n is legal. The model's VALUE_BLINDING generator association is a
    named global/source boundary; no desired contribution or inverse is input.
    Actual callers must first emit the genuine126 completion modules.
    """
    C='RuntimeBalanceBlindingFixedCompletion'
    B='RuntimeBalanceBlindingCanonical'
    R='RuntimeBalanceBlindingCanonicalCompletion'
    A='RuntimeBalanceBlindingFixed'
    P=[f'RuntimeBalanceBlindingWindow{i:03d}Program' for i in range(126)]
    bit=lambda index:f'(encodeBits 252 n)[{index}]?.getD false'
    source=f'''import ShielddSecurity.{C}
namespace ShielddSecurity.RuntimeBalanceBlindingNativeScalar
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
theorem decoded_preserved {{F : Type}} [Field F] (base : Nat → F) (n : Nat) :
    {A}.decodedBits ({C}.construct base n) = {B}.decodedBits ({R}.construct base n) := by
  classical
  have protection : ∀ program ∈ {C}.programs n,
      GroupFixedCircuitCompletion.Protected {C}.kept program := by
    intro program member
    simp only [{C}.programs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in P)}
'''
    for i,p in enumerate(P):
        source+=f'    · exact {p}.caller_protected ({bit(2*i)}) ({bit(2*i+1)})\n'
    source+=f'''  have supports : {B}.bits.all (fun terms => terms.all
      (fun term => decide (term.1 ∈ {C}.kept))) = true := by decide
  change ScalarBits.decodeBits ({C}.construct base n) {B}.bits =
    ScalarBits.decodeBits ({R}.construct base n) {B}.bits
  unfold ScalarBits.decodeBits
  apply List.map_congr_left
  intro terms member
  have values : eval ({C}.construct base n) terms = eval ({R}.construct base n) terms := by
    apply eval_agrees
    intro term present
    have kept := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp supports terms member) term present)
    exact GroupFixedCircuitCompletion.run_preserves ({R}.construct base n) ({C}.programs n)
      {C}.kept protection term.1 kept
  simp only [ScalarBits.decodeBit,values]
theorem actual_native_scalar_complete {{F J : Type}} [Field F] [CharP F {A}.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : eval base {B}.privateValue = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (model : Group.StandardCurveModel J ({A}.coefficientD : F))
    (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F)) (imaginarySquare : imaginary*imaginary = -1)
    (valueBlinding : J) (valueBlindingRole : ({A}.generator : Group.Point F) = model.coordinates valueBlinding)
    (linked : base 200692 = base 0) :
    Satisfies ({C}.construct base n) {A}.rawRows ∧
      {A}.contribution ({C}.construct base n) = model.coordinates (n • valueBlinding) := by
  have constructed := {C}.actual_rows_complete base n canonical
    (by simpa only [{B}.privateValue,eval,Int.cast_one,one_mul,add_zero] using meaning)
    one four imaginary nonSquare imaginarySquare linked
  have canonicalBits := {R}.constructs base n canonical
    (by simpa only [{B}.privateValue,eval,Int.cast_one,one_mul,add_zero] using meaning) one four
  have finalOne : {C}.construct base n 0 = 1 := (constructed.2.2 0 (by decide)).trans one
  have coordinates := {A}.actual_fixed_scalar ({C}.construct base n) finalOne imaginary model
    nonSquare imaginarySquare valueBlinding valueBlindingRole constructed.1
  have integer : binary ({B}.decodedBits ({R}.construct base n)) = n := canonicalBits.2.1
  rw [decoded_preserved base n,integer] at coordinates
  exact ⟨constructed.1,coordinates⟩
#print axioms decoded_preserved
#print axioms actual_native_scalar_complete
end ShielddSecurity.RuntimeBalanceBlindingNativeScalar
'''
    return _signature_audits(source)


def generate(qualified_parent, raw_pages, expected_base, expected_blinding, extracted,
             readonly_lcs=(), *, include_local=False, include_native_scalar=False):
    if type(include_local) is not bool or type(include_native_scalar) is not bool:
        raise relation.RelationError('blinding126 typed local generation flag')
    accepted = plan(qualified_parent,raw_pages,expected_base,expected_blinding,extracted,readonly_lcs)
    chunks = accepted['checked']['chunks']; prefix='RuntimeBalanceBlinding'
    windows=[prefix+f'Window{i:03d}' for i in range(126)]
    pages=[prefix+f'Chunk{item["metadata"]["window_start"]:03d}' for item in chunks]
    result=scalar.generate(qualified_parent,raw_pages,expected_base,expected_blinding,
                          extracted['canonical'],readonly_lcs=readonly_lcs)
    for ordinal,page in enumerate(chunks):
        start=page['metadata']['window_start'];count=page['metadata']['window_count']
        result[pages[ordinal]]=renderer.render_chunk(page,namespace=pages[ordinal],window_stems=windows[start:start+count])
        for offset in range(count):
            index=start+offset
            result[windows[index]+'Program']=renderer._window_program_source(page,
                accepted['bounds']['frames'][index],accepted['bounds'],accepted['loop']['kept'],offset,stem=windows[index])
            if include_local:
                for name,body in local.generate_window(page,accepted['selections'][ordinal],offset,readonly_lcs=readonly_lcs):
                    result[name]=body
    result[prefix+'Fixed']=_description(renderer.render_full(chunks,namespace=prefix+'Fixed',
        canonical_namespace=prefix+'Canonical',chunk_stems=pages,window_stems=windows))
    result[prefix+'FixedCompletion']=renderer.render_full_completion(accepted['loop'],accepted['bounds'],
        accepted['canonical'],chunks,namespace=prefix+'FixedCompletion',sound_namespace=prefix+'Fixed',
        canonical_namespace=prefix+'Canonical',order_namespace=prefix+'CanonicalOrder',
        scalar_completion_namespace=prefix+'CanonicalCompletion',window_stems=windows,chunk_stems=pages
        ).replace('spendAuthRole','valueBlindingRole').replace('spendAuth','valueBlinding')
    result[prefix+'FixedFrame']=frame_source(accepted['canonical']['bit_start'])
    if include_native_scalar:
        result[prefix+'NativeScalar']=native_scalar_source()
    return result
