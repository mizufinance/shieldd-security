"""Strict EPK entry points to neutral fixed-window proof rendering.

Production pages/qualifier/replay must be independently accepted. No spend
schema is invented, and no native EPK/canonical endpoint is assumed from rows.
Local curve constructors derive division legality; whole126 and six-scope
composition, SDK Fr/parameter association and original outside-frame remain
separate obligations.
"""
from . import transfer_epk_fixed as epk, transfer_epk_fixed_batch as batch
from . import transfer_epk_fixed_completion as completion
from . import generate_transfer_fixed_spend as renderer, transfer_relation as relation
from . import transfer_epk_fixed_canonical as canonical


def _selection(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
               scope_id,page_index,window_offset,readonly_lcs):
    if (type(scope_id)is not int or not 0<=scope_id<6 or
            type(page_index)is not int or not 0<=page_index<8 or
            type(window_offset)is not int or not 0<=window_offset<16):
        raise relation.RelationError('EPK fixed renderer exact scope/page/window indices')
    checked=epk.inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles)
    selected=batch.page_selection(checked,extracted,8*scope_id+page_index)
    page=checked['scopes'][scope_id]['chunks'][page_index]
    raw,normalized,products,quotients=completion.selection(page,selected)
    plan=completion.completion_plan(page,selected,accepted_capsules,accepted_roles,readonly_lcs=readonly_lcs)
    if window_offset>=plan['window_count']:
        raise relation.RelationError('EPK fixed renderer final bounded page offset')
    stem=f'RuntimeTransferEpk{scope_id}FixedWindow{plan["windows"][window_offset]["index"]:03d}'
    return page,raw,normalized,products,quotients,plan,stem


def generate_window(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
                    scope_id,page_index=0,window_offset=0,*,readonly_lcs=()):
    """Soundness and exact native-table transport; requires actual row truth."""
    page,raw,normalized,products,quotients,plan,stem=_selection(qualified_parent,raw_pages,
        accepted_capsules,accepted_roles,extracted,scope_id,page_index,window_offset,readonly_lcs)
    return renderer.render_window(page,raw,normalized,products,quotients,window_offset,stem=stem)


def generate_window_completion(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
                    scope_id,page_index=0,window_offset=0,*,readonly_lcs=()):
    """Local mixed-row constructor. Its local denominators remain explicit."""
    page,raw,normalized,products,quotients,plan,stem=_selection(qualified_parent,raw_pages,
        accepted_capsules,accepted_roles,extracted,scope_id,page_index,window_offset,readonly_lcs)
    return renderer.render_window_completion(page,raw,normalized,plan,window_offset,stem=stem)


def generate_window_complete(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
                    scope_id,page_index=0,window_offset=0,*,readonly_lcs=()):
    """Construct local rows and outgoing curve; derives local denominators.

    Native table constants, incoming curve and constructed bit meanings are
    separate exact upstream inputs. No Satisfies/output/nonidentity premise.
    """
    page,raw,normalized,products,quotients,plan,stem=_selection(qualified_parent,raw_pages,
        accepted_capsules,accepted_roles,extracted,scope_id,page_index,window_offset,readonly_lcs)
    return renderer.render_window_complete(page,plan,window_offset,stem=stem)


def generate_canonical(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id):
    """Return exact sound/order/original-constructor source for one actual scope.

    The comparator bit block is seeded by the admitted SDK Fr integer. Its
    endpoint and original assertions follow from construction and integer
    bounds. Capture/row matching alone never supplies the native scalar law.
    No production source is generated until strict qualified ingress succeeds.
    """
    if type(scope_id)is not int or not 0<=scope_id<6:
        raise relation.RelationError('EPK canonical renderer exact scope index')
    checked,selected,plan=_canonical_plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id)
    sound=f'RuntimeTransferEpk{scope_id}Canonical';order=sound+'Order';complete=sound+'Completion'
    order_source=renderer.render_randomizer_order(plan,namespace=order,kept_block_size=256)
    complete_source=renderer.render_randomizer_bit_completion(selected['checked'],plan,
        namespace=complete,order_namespace=order,sound_namespace=sound,kept_block_size=256)
    sound_source=canonical.generate(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id)
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
    sound_source=sound_source.replace(f'end ShielddSecurity.{sound}',extra+f'end ShielddSecurity.{sound}')
    return {sound:sound_source,order:order_source,complete:complete_source}


def _canonical_plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,scope_id):
    """Strict shared constructor data, reused by the full loop renderer."""
    if type(scope_id)is not int or not 0<=scope_id<6:
        raise relation.RelationError('EPK canonical renderer exact scope index')
    checked=epk.inspect_all_pages(qualified_parent,raw_pages,accepted_capsules,accepted_roles)
    whole=canonical.construction_plan(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted)
    selected,certificate,expected,raw,normalized=canonical._selection(checked,extracted,scope_id)
    scope=whole['scopes'][scope_id];bits=set(scope['bits'])
    own=bits|{column for stage in scope['stages'] for column in (stage['output'],stage['auxiliary'])}
    kept=set(whole['protected'])|(set(whole['writes'])-own)
    for owner in (accepted_capsules,accepted_roles):
        kept.update(column for terms in owner['observed'].values() for column,_ in terms if column not in bits)
    if kept&own:raise relation.RelationError('EPK canonical writes alias native/caller readonly roles')
    stages=[dict(stage,step=index) for index,stage in enumerate(scope['stages'],1)]
    plan=dict(value=scope['value'],bit_start=scope['start'],width=252,stages=stages,
        chunks=[stages[i:i+16] for i in range(0,len(stages),16)],kept=sorted(kept))
    plan['rows']=scope['original_rows']
    return checked,selected,plan
