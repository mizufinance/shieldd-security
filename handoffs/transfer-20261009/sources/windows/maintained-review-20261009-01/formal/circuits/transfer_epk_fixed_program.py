"""Full fixed126 constructors from one independently qualified EPK row union.

No observer stage is activated here. All actual source/row/canonical/native
association and frame conditions are retained; unsupported allocation refuses.
"""
from . import transfer_epk_fixed_composition as composition,transfer_epk_fixed_batch as batch
from . import transfer_epk_fixed_rows as boundaries,transfer_epk_fixed_completion as local
from . import generate_transfer_epk_fixed_completion as epk_render
from . import generate_transfer_fixed_spend as render,transfer_fixed_spend as fixed
from . import transfer_arithmetic as arithmetic,transfer_relation as relation
from .transfer_balance_rows import source_index
from .generate_hash_round import _signature_audits
from . import generate_transfer_epk_native_boundary as native_boundary


def plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id):
    """Exact local constructors, dual allocation cursors and native role data."""
    if not isinstance(extracted,dict) or set(extracted)!={'fixed','canonical','boundaries',
            'parent_sha256','raw_page_sha256','ordinary_replays','scope'} or type(extracted['ordinary_replays'])is not int or extracted['ordinary_replays']!=1:
        raise relation.RelationError('EPK full constructor one exact original row union')
    checked,scalar,randomizer=epk_render._canonical_plan(qualified_parent,raw_pages,accepted_capsules,
        accepted_roles,extracted['canonical'],scope_id)
    if extracted['parent_sha256']!=checked['parent_sha256'] or extracted['raw_page_sha256']!=checked['raw_page_sha256']:
        raise relation.RelationError('EPK full constructor parent/raw page union identity')
    programs=composition.plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted['fixed'])
    inverse=boundaries.boundary_plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted['boundaries'])
    boundary_raw=boundaries._certificates(checked,extracted['boundaries'])[0]
    if any(child['identity']!=extracted['canonical']['identity'] for child in (extracted['fixed'],extracted['boundaries'])):
        raise relation.RelationError('EPK full constructor same full ordinary identity')
    chunks=checked['scopes'][scope_id]['chunks'];loop=programs['loops'][scope_id]
    raw={};selected=[]
    # Normalize_selection already validates raw terms; retain actual field terms
    # directly rather than identify rows by hashes or independent role names.
    raw.update(arithmetic.normalize_selection(extracted['canonical']['scopes'][scope_id],
        scalar['checked']['metadata'],scalar['checked']['metadata_sha256'])[0])
    for local_index,chunk in enumerate(chunks):
        selection=batch.page_selection(checked,extracted['fixed'],8*scope_id+local_index)
        current=local.selection(chunk,selection)[0]
        for index,row in current.items():
            if index in raw and raw[index]!=row:raise relation.RelationError('EPK full constructor cross-page/canonical original row disagreement')
            raw[index]=row
        selected.append(selection)
    frames=[]
    start=randomizer['bit_start']
    for program in loop['programs']:
        index=program['index'];page=chunks[index//16]
        bit_support=[]
        for axis,bit in enumerate(page['metadata']['bits'][2*index:2*index+2]):
            terms=page['observed'][source_index(bit)]
            if terms!=((start+2*index+axis,1),):raise relation.RelationError('EPK full constructor exact canonical/fixed singleton bits')
            bit_support.extend(c for c,_ in terms)
        frames.append(dict(program,bit_support=bit_support))
    bounds=fixed._completion_frames(frames,raw,randomizer['rows'],randomizer,checked['parent']['constant_copy'])
    inverse_writes={inverse['scopes'][scope_id]['inverse_constructor'][key] for key in ('quotient','product','auxiliary')}
    earlier_writes=set(loop['writes'])|set(range(randomizer['bit_start'],randomizer['bit_start']+252))
    earlier_writes.update(c for stage in randomizer['stages'] for c in (stage['output'],stage['auxiliary']))
    if inverse_writes&earlier_writes:raise relation.RelationError('EPK native inverse writes alias earlier constructor writes')
    if any(c in inverse_writes for row in raw.values() for terms in row for c,_ in terms):
        raise relation.RelationError('EPK native inverse writes destroy original fixed/canonical row support')
    retained={key:checked[key] for key in ('parent','parent_sha256','raw_page_sha256')}
    return dict(checked=retained,chunks=chunks,selections=selected,loop=loop,scalar=randomizer,bounds=bounds,
        boundary=inverse['scopes'][scope_id],boundary_raw=boundary_raw,identity=extracted['fixed']['identity'],
        parent_sha256=checked['parent_sha256'],raw_page_sha256=checked['raw_page_sha256'],
        scope='Exact126 constructive source inputs/native table trace only; actual kernel/native caller and independent all-row frame OPEN')


def generate_scope(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id,*,include_local=False):
    """Render strict actual scope consumers, never fabricate capture metadata."""
    if type(include_local)is not bool:raise relation.RelationError('EPK constructor local rendering Boolean flag')
    accepted=plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id)
    chunks=accepted['chunks'];loop=accepted['loop'];bounds=accepted['bounds'];scalar=accepted['scalar']
    stem=f'RuntimeTransferEpk{scope_id}';canonical=stem+'Canonical';sound=stem+'Fixed'
    windows=[stem+f'FixedWindow{i:03d}' for i in range(126)]
    pages=[stem+f'FixedChunk{chunk["metadata"]["window_start"]:03d}' for chunk in chunks]
    result=epk_render.generate_canonical(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted['canonical'],scope_id)
    for ordinal,(chunk,selection) in enumerate(zip(chunks,accepted['selections'])):
        start=chunk['metadata']['window_start'];size=chunk['metadata']['window_count']
        result[pages[ordinal]]=render.render_chunk(chunk,namespace=pages[ordinal],window_stems=windows[start:start+size])
        local_plan=local.completion_plan(chunk,selection,accepted_capsules,accepted_roles)
        raw,normalized,products,quotients=local.selection(chunk,selection)
        for offset in range(size):
            index=start+offset
            result[windows[index]+'Program']=render._window_program_source(chunk,bounds['frames'][index],bounds,loop['kept'],offset,stem=windows[index])
            if include_local:
                result[windows[index]]=render.render_window(chunk,raw,normalized,products,quotients,offset,stem=windows[index])
                result[windows[index]+'Completion']=render.render_window_completion(chunk,raw,normalized,local_plan,offset,stem=windows[index])
                result[windows[index]+'CurveCompletion']=render.render_window_complete(chunk,local_plan,offset,stem=windows[index])
    result[sound]=render.render_full(chunks,namespace=sound,canonical_namespace=canonical,chunk_stems=pages,window_stems=windows)
    result[sound+'Completion']=render.render_full_completion(loop,bounds,scalar,chunks,namespace=sound+'Completion',
        sound_namespace=sound,canonical_namespace=canonical,order_namespace=canonical+'Order',
        scalar_completion_namespace=canonical+'Completion',window_stems=windows,chunk_stems=pages)
    result[sound+'Frame']=_frame_source(scope_id,scalar['bit_start'])
    result[sound+'NativeEndpoint']=_native_endpoint_source(accepted,scope_id)
    result[stem+'NativeBoundary']=native_boundary.generate(accepted,scope_id)
    return result


def _frame_source(scope_id,start):
    """Universal support transport; no desired row/output or Satisfies premise."""
    stem=f'RuntimeTransferEpk{scope_id}';ns=stem+'FixedFrame'
    C='ShielddSecurity.'+stem+'FixedCompletion';O='ShielddSecurity.'+stem+'CanonicalOrder'
    source=f'''import {C}
import ShielddSecurity.PoseidonCompletion
namespace ShielddSecurity.{ns}
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
    (ShielddSecurity.{stem}CanonicalCompletion.construct base n) ({C}.programs n) [column]
    preserved column (List.mem_singleton_self column)
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
end ShielddSecurity.{ns}
'''
    return _signature_audits(source)


def _native_endpoint_source(accepted,scope_id):
    """Construct native supplied witnesses, then derive the computed endpoint.

    The standard generator/table interpretation is global. Scalar meaning is
    the independently admitted native input, not a promised curve output.
    """
    published=accepted['boundary']['published'];value=accepted['scalar']['value']
    if any(len(terms)!=1 or terms[0][1]!=1 for terms in published):
        raise relation.RelationError('EPK native publication exact singleton witnesses')
    x,y=(terms[0][0] for terms in published);copy=accepted['checked']['parent']['constant_copy']
    if len({x,y,value,0,1,2,copy})!=7 or {x,y}&set(accepted['loop']['writes']):
        raise relation.RelationError('EPK native seed writes alias scalar/public/committed/copy/fixed outputs')
    stem=f'RuntimeTransferEpk{scope_id}';ns=stem+'FixedNativeEndpoint'
    A='ShielddSecurity.'+stem+'Fixed';C=A+'Completion';B='ShielddSecurity.'+stem+'Canonical'
    source=f'''import {C}
import ShielddSecurity.GroupNativeGenerator
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 350000
set_option maxRecDepth 4096
def seedWrites : List Nat := [{x},{y}]
def seed {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) :=
  patchAssignment base (fun column => if column = {x} then (model.coordinates (n • generator)).x
    else (model.coordinates (n • generator)).y) seedWrites
def construct {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) :=
  {C}.construct (seed base model generator n) n
theorem seed_outside {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n column : Nat)
    (outside : column ∉ seedWrites) : seed base model generator n column = base column :=
  patchAssignment_preserves base _ seedWrites column outside
theorem seed_published {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) :
    seed base model generator n {x} = (model.coordinates (n • generator)).x ∧
      seed base model generator n {y} = (model.coordinates (n • generator)).y := by
  simp [seed,seedWrites,patchAssignment]
theorem rows_complete {{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (linked : base {copy} = base 0) : Satisfies (construct base model generator n) {A}.rawRows := by
  have scalar : seed base model generator n {value} = (n : F) :=
    (seed_outside base model generator n {value} (by decide)).trans meaning
  have unit : seed base model generator n 0 = 1 :=
    (seed_outside base model generator n 0 (by decide)).trans one
  have copyLink : seed base model generator n {copy} = seed base model generator n 0 := by
    rw [seed_outside base model generator n {copy} (by decide),
      seed_outside base model generator n 0 (by decide),linked]
  exact ({C}.actual_rows_complete (seed base model generator n) n canonical scalar unit four
    imaginary nonSquare imaginarySquare copyLink).1
theorem native_coordinates {{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (parameter : ({A}.generator : Group.Point F) = model.coordinates generator)
    (linked : base {copy} = base 0) :
    {A}.contribution (construct base model generator n) = model.coordinates (n • generator) := by
  let initial := seed base model generator n
  have initialScalar : initial {value} = (n : F) :=
    (seed_outside base model generator n {value} (by decide)).trans meaning
  have initialOne : initial 0 = 1 := (seed_outside base model generator n 0 (by decide)).trans one
  have initialLink : initial {copy} = initial 0 := by
    rw [seed_outside base model generator n {copy} (by decide),
      seed_outside base model generator n 0 (by decide),linked]
  have completed := {C}.actual_rows_complete initial n canonical initialScalar initialOne four
    imaginary nonSquare imaginarySquare initialLink
  have oneBuilt : construct base model generator n 0 = 1 :=
    (completed.2.2 0 (by decide)).trans initialOne
  have valueBuilt : eval (construct base model generator n) {B}.privateValue = (n : F) := by
    simpa only [{B}.privateValue,eval,Int.cast_one,one_mul,add_zero] using
      (completed.2.2 {value} (by decide)).trans initialScalar
  have result := {A}.actual_fixed_canonical (construct base model generator n) oneBuilt four
    imaginary model nonSquare imaginarySquare generator parameter completed.1
  have exactScalar : binary ({A}.decodedBits (construct base model generator n)) = n :=
    bounded_cast_injective (result.1.trans (by decide : Scalar.order < Scalar.modulus))
      (canonical.trans (by decide : Scalar.order < Scalar.modulus)) (result.2.1.trans valueBuilt)
  simpa only [exactScalar] using result.2.2
theorem published_equal {{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : base {value} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (parameter : ({A}.generator : Group.Point F) = model.coordinates generator)
    (linked : base {copy} = base 0) :
    (⟨construct base model generator n {x},construct base model generator n {y}⟩ : Group.Point F) =
      {A}.contribution (construct base model generator n) := by
  rw [native_coordinates base n canonical meaning one four imaginary nonSquare imaginarySquare
    model generator parameter linked]
  have initialScalar := (seed_outside base model generator n {value} (by decide)).trans meaning
  have initialOne := (seed_outside base model generator n 0 (by decide)).trans one
  have initialLink : seed base model generator n {copy} = seed base model generator n 0 := by
    rw [seed_outside base model generator n {copy} (by decide),
      seed_outside base model generator n 0 (by decide),linked]
  have completed := {C}.actual_rows_complete (seed base model generator n) n canonical initialScalar
    initialOne four imaginary nonSquare imaginarySquare initialLink
  have supplied := seed_published base model generator n
  apply congrArg₂ Group.Point.mk
  · exact (completed.2.2 {x} (by decide)).trans supplied.1
  · exact (completed.2.2 {y} (by decide)).trans supplied.2
theorem native_x_nonzero {{F J : Type}} [Field F] [AddCommGroup J]
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (exactOrder : addOrderOf generator = Scalar.order) (n : Nat)
    (positive : 0 < n) (canonical : n < Scalar.order) : (model.coordinates (n • generator)).x ≠ 0 := by
  have inverse := GroupNativeGenerator.canonical_multiple_inverse ({A}.coefficientD : F)
    model generator exactOrder n positive canonical
  intro zero
  rw [zero,zero_mul] at inverse
  exact zero_ne_one inverse
#print axioms seed_outside
#print axioms seed_published
#print axioms rows_complete
#print axioms native_coordinates
#print axioms published_equal
#print axioms native_x_nonzero
end ShielddSecurity.{ns}
'''
    return _signature_audits(source)
