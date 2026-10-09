"""Callable bounded recipe for the actual74 and full nonidentity captures.

The maintained CLI owns admission and accepted caller construction. This module
does not qualify a capture, execute a runtime/compiler, generate a certificate,
or assume witness values. Each replay consumes the full original ordered stream
through the component's existing strict extractor, retaining raw parent/page
identity separately from the qualified in-memory parser view.
"""
import hashlib
from circuits import transfer_relation as relation
from circuits import transfer_t4_pages as pages, transfer_recovery_pages as recovery_pages
from circuits import transfer_asset_generator_nonidentity as generator
from circuits import transfer_asset_map as maps, transfer_note_spend as spend
from circuits import transfer_note_tree as tree, transfer_note_ranges as ranges
from circuits import transfer_note_outputs as outputs, transfer_note_hash as input_hash
from circuits import transfer_note_output_hash as output_hash, transfer_asset_hash as asset_hash
from circuits import transfer_recovery_capsule as capsules, transfer_recovery_hash as recovery_hash
from circuits import transfer_recovery_ranges as recovery_ranges


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def tasks():
    """Explicit local replay coverage; this list is not a full Transfer claim."""
    return [('asset-map', None), ('asset-inverse', None), ('spend', None), ('outputs', None),
            *[('input-range', i) for i in range(4)],
            *[('output-range', i) for i in range(2)],
            *[('tree', i) for i in range(48)],
            *[('input-hash', i) for i in range(55)],
            *[('output-hash', i) for i in range(55, 63)],
            ('asset-hash', 63),
            *[('output-hash-binding', i) for i in (56, 58, 60, 62)],
            *[('recovery-hash', i) for i in range(65, 73)],
            ('recovery-bindings', None), ('recovery-inverses', None)]


def _task(kind, index):
    if not isinstance(kind, str) or index is not None and type(index) is not int:
        raise relation.RelationError('actual ingress task type')
    if (kind, index) not in tasks() + [('recovery-range', 0), ('recovery-range', 1)]:
        raise relation.RelationError('actual ingress unsupported local task')


def prepare_parents(manifest_data, roles64_data, roles73_data, nonidentity_data, accepted_roles):
    """Recheck original qualified parents and exact pending roles on each use.

accepted_roles must come from the maintained caller's independent acceptance;
this function deliberately accepts no serialized assertion of caller success.
"""
    prefix = recovery_pages.qualified_prefix65_view(manifest_data, accepted_roles['metadata']['relation_digest'])
    roles = pages.qualified_roles(prefix['parent_data'], roles64_data, accepted_roles)
    capsule_data, capsule_sha = recovery_pages.qualified_roles(
        manifest_data, roles73_data, roles['output_data'], accepted_roles)
    map_view = None
    if nonidentity_data is not None:
        map_view = generator.derived_map_view(nonidentity_data, accepted_roles)
        map_checked = maps.inspect_metadata(map_view['map_data'], accepted_roles)
        for key in pages.IDENTITY:
            if map_checked['metadata'][key] != prefix['parent_manifest'][key]:
                raise relation.RelationError('actual74/nonidentity full relation identity mismatch')
    return dict(prefix=prefix, roles=roles, recovery_data=capsule_data,
                recovery_pending_sha256=capsule_sha, map_view=map_view)


def _map_data(context, kind):
    view = context['map_view']
    if view is None:
        if kind in ('asset-map', 'asset-inverse', 'asset-hash'):
            raise relation.RelationError('actual asset component requires qualified nonidentity parent')
        return None
    return view['map_data']


def _parent_ids(context):
    identities = {'actual74': context['prefix']['parent_metadata_sha256'],
                  'roles64_pending': context['roles']['original_pending_sha256'],
                  'roles73_pending': context['recovery_pending_sha256']}
    if context['map_view'] is not None:
        identities['nonidentity'] = context['map_view']['parent_metadata_sha256']
    return identities


def _receipt(kind, index, extracted, *, parents, pending_page=None, parser_view=None):
    identity = extracted.get('identity')
    if not isinstance(identity, dict) or not isinstance(identity.get('raw_sha256'), str):
        raise relation.RelationError('actual ingress missing independent full row replay')
    return dict(kind='actual-component-row-ingress', component=kind, index=index,
                parent_sha256=parents, pending_page_sha256=None if pending_page is None else _sha(pending_page),
                parser_view_sha256=None if parser_view is None else _sha(parser_view),
                original_row_stream_sha256=identity['raw_sha256'], extraction=extracted,
                scope='original full ordered row replay and local selection; kernels/native/composition open')


def replay_asset(nonidentity_data, stream, accepted_roles, kind):
    """One complete ordinary-row replay for map or final inverse, no74 needed."""
    _task(kind, None)
    if kind not in ('asset-map', 'asset-inverse'):
        raise relation.RelationError('actual asset replay component required')
    projected = generator.derived_map_view(nonidentity_data, accepted_roles)
    if kind == 'asset-map':
        view = projected['map_data']
        extracted = maps.extract(view, stream, accepted_roles)
        maps.certificates(view, extracted, accepted_roles)
    else:
        view = nonidentity_data
        extracted = generator.extract(view, stream, accepted_roles)
        generator.certificates(view, extracted, accepted_roles)
    return _receipt(kind, None, extracted, parents={'nonidentity': projected['parent_metadata_sha256']}, parser_view=view)


def replay_t4(manifest_data, roles64_data, roles73_data, nonidentity_data, stream,
              accepted_roles, parameter_root, kind, index=None, page_data=None):
    """Run one selected local task, loading at most one permutation page.

The caller opens a new full stream for every task. Persist each returned bounded
selection and discard it before the next task. Parameter files are independently
checked by the hash component; parent hashes never replace that correspondence.
"""
    _task(kind, index)
    context = prepare_parents(manifest_data, roles64_data, roles73_data, nonidentity_data, accepted_roles)
    roles = context['roles']; note = roles['note_data']; output = roles['output_data']
    recovery = context['recovery_data']; map_data = _map_data(context, kind)
    view = None
    hash_task = kind in ('input-hash', 'output-hash', 'asset-hash', 'output-hash-binding', 'recovery-hash')
    if not hash_task and page_data is not None:
        raise relation.RelationError('actual ingress unexpected page bytes')
    if kind in ('asset-map', 'asset-inverse'):
        asset = replay_asset(nonidentity_data, stream, accepted_roles, kind)
        extracted = asset['extraction']; view = map_data if kind == 'asset-map' else nonidentity_data
    elif kind == 'spend':
        extracted = spend.extract(note, stream, accepted_roles); spend.certificates(note, extracted, accepted_roles); view = note
    elif kind == 'outputs':
        extracted = outputs.extract(output, stream, accepted_roles); outputs.certificates(output, extracted, accepted_roles); view = output
    elif kind == 'input-range':
        slot, role = divmod(index, 2); role = ('amount', 'position')[role]
        extracted = ranges.extract(note, stream, accepted_roles, slot, role); view = note
    elif kind == 'output-range':
        extracted = outputs.extract_range(output, stream, accepted_roles, index); view = output
    elif kind == 'tree':
        slot, level = divmod(index, 24); view = roles['tree_data']
        extracted = tree.extract_level(view, stream, note, accepted_roles, slot, level)
        tree.certificates(view, extracted, note, accepted_roles)
    elif kind == 'recovery-bindings':
        extracted = capsules.extract_bindings(recovery, stream, output, accepted_roles)
        capsules.certificates(recovery, extracted, output, accepted_roles); view = recovery
    elif kind == 'recovery-inverses':
        extracted = capsules.extract_inverses(recovery, stream, output, accepted_roles)
        capsules.inverse_certificates(recovery, extracted, output, accepted_roles); view = recovery
    elif kind == 'recovery-range':
        extracted = recovery_ranges.extract(recovery, stream, output, accepted_roles, index); view = recovery
    elif kind == 'input-hash':
        view = pages.qualified_input_hash(manifest_data, page_data, index, roles['tree_data'], note, accepted_roles)
        extracted = input_hash.extract(view, stream, note, accepted_roles, parameter_root)
        input_hash.round_selection(view, extracted, note, accepted_roles, parameter_root)
    elif kind in ('output-hash', 'output-hash-binding'):
        view = pages.qualified_output_hash(manifest_data, page_data, index, output, accepted_roles)
        if kind == 'output-hash-binding':
            extracted = output_hash.extract_binding(view, stream, output, accepted_roles)
        else:
            extracted = output_hash.extract(view, stream, output, accepted_roles, parameter_root)
            output_hash.round_selection(view, extracted, output, accepted_roles, parameter_root)
    elif kind == 'asset-hash':
        view = pages.qualified_asset_hash(manifest_data, page_data, nonidentity_data, accepted_roles)
        extracted = asset_hash.extract(view, stream, map_data, accepted_roles, parameter_root)
        asset_hash.round_selection(view, extracted, map_data, accepted_roles, parameter_root)
    else:
        view = recovery_pages.qualified_hash(manifest_data, page_data, index, recovery, output, accepted_roles, parameter_root)
        extracted = recovery_hash.extract(view, stream, recovery, output, accepted_roles, parameter_root)
        recovery_hash.round_selection(view, extracted, recovery, output, accepted_roles, parameter_root)
    return _receipt(kind, index, extracted, parents=_parent_ids(context),
                    pending_page=page_data, parser_view=view)


def tasks_with_recovery_ranges():
    """Fresh138-task successor; retain the frozen136-task baseline list."""
    return tasks() + [('recovery-range', 0), ('recovery-range', 1)]


def tasks_with_recovery_canonical():
    """Optional140 local scopes; both new slots share one complete replay."""
    return tasks_with_recovery_ranges() + [('recovery-canonical', 0), ('recovery-canonical', 1)]


def replay_recovery_canonical(manifest_data, roles64_data, roles73_data, stream, accepted_roles):
    """Derive both comparator chains from qualified parents and one stream."""
    from circuits import transfer_recovery_canonical as canonical
    context = prepare_parents(manifest_data, roles64_data, roles73_data, None, accepted_roles)
    data = context['recovery_data']; output = context['roles']['output_data']
    extracted = canonical.extract(data, stream, output, accepted_roles)
    return _receipt('recovery-canonical', None, extracted, parents=_parent_ids(context), parser_view=data)


def generate_recovery_canonical(manifest_data, roles64_data, roles73_data, accepted_roles, receipt):
    """Reaccept retained derivative certificates; emit exactly two candidates."""
    from circuits import transfer_recovery_canonical as canonical
    context = prepare_parents(manifest_data, roles64_data, roles73_data, None, accepted_roles)
    data = context['recovery_data']; output = context['roles']['output_data']
    if (not isinstance(receipt, dict) or receipt.get('kind') != 'actual-component-row-ingress'
            or receipt.get('component') != 'recovery-canonical' or receipt.get('index') is not None
            or receipt.get('parent_sha256') != _parent_ids(context)
            or receipt.get('parser_view_sha256') != _sha(data)):
        raise relation.RelationError('actual recovery canonical receipt identity')
    for slot in (0, 1):
        yield f'RuntimeTransferRecovery{slot}Canonical', canonical.generate(
            data, receipt['extraction'], output, accepted_roles, slot)


def replay_remaining(manifest_data, page_data, stream, accepted_roles,
                     parameter_root, kind, ordinal):
    """New remaining schema through the same original-row component receipt.

    The caller opens a fresh full ordinary stream for each local task. The
    already qualified parent, exact roles/LCs and native/DAG interpretation are
    rechecked before extraction; no serialized replay-success assertion is read.
    """
    from circuits import transfer_remaining_pages as remaining
    if kind not in ('remaining-hash', 'remaining-metadata-equalities', 'remaining-tree-level', 'remaining-tree-position', 'remaining-membership') or type(ordinal) is not int:
        raise relation.RelationError('remaining actual ingress task type')
    if kind == 'remaining-metadata-equalities':
        if ordinal != 0:
            raise relation.RelationError('remaining metadata equality role page required')
        extracted = remaining.extract_metadata_equalities(manifest_data, page_data, stream, accepted_roles)
        remaining.metadata_certificates(manifest_data, page_data, extracted, accepted_roles)
    elif kind == 'remaining-membership':
        if ordinal != 0:
            raise relation.RelationError('remaining membership role page required')
        extracted = remaining.extract_membership(manifest_data, page_data, stream, accepted_roles)
        remaining.membership_certificates(manifest_data, page_data, extracted, accepted_roles)
    elif kind == 'remaining-tree-position':
        if ordinal != 0:
            raise relation.RelationError('remaining tree position role page required')
        extracted = remaining.extract_tree_position(manifest_data, page_data, stream, accepted_roles)
        remaining.tree_position_certificates(manifest_data, page_data, extracted, accepted_roles)
    elif kind == 'remaining-tree-level':
        # ordinal identifies a level in the page-zero ordered role record, not
        # a hash/permutation page. Its scope and depth are rechecked by parser.
        extracted = remaining.extract_tree_level(manifest_data, page_data, ordinal, stream, accepted_roles)
        remaining.tree_level_certificates(manifest_data, page_data, ordinal, extracted, accepted_roles)
    else:
        if ordinal == 0:
            raise relation.RelationError('remaining actual permutation page required')
        extracted = remaining.extract_hash(manifest_data, page_data, ordinal, stream, accepted_roles, parameter_root)
    return _receipt(kind, ordinal, extracted,
                    parents={'remaining': _sha(manifest_data), 'accepted_caller': accepted_roles['metadata_sha256']},
                    pending_page=page_data)


def replay_remaining_tree_bundle(manifest_data, page_data, stream, accepted_roles):
    """Three strict compliance slices, sharing exactly one original-row pass."""
    from circuits import transfer_remaining_tree_bundle as bundle
    extracted=bundle.extract(manifest_data,page_data,stream,accepted_roles)
    return _receipt('remaining-tree-bundle',0,extracted,
                    parents={'remaining':_sha(manifest_data),'accepted_caller':accepted_roles['metadata_sha256']},
                    pending_page=page_data)


def typed_hash_context(manifest_data, roles64_data, roles73_data, nonidentity_data,
                       accepted_roles, parameter_root, kind, index, page_data, extracted):
    """Reaccept one exact page/selection through its own typed hash parser.

This is a generator input, not a transport certificate or runtime qualifier.
The native generator receives exact source/row/parameter contexts independently
for the template and actual page. Hash outputs stay constructive consumers.
"""
    _task(kind, index)
    context = prepare_parents(manifest_data, roles64_data, roles73_data, nonidentity_data, accepted_roles)
    roles = context['roles']; note = roles['note_data']; output = roles['output_data']
    recovery = context['recovery_data']; map_data = _map_data(context, kind)
    if kind == 'input-hash':
        view = pages.qualified_input_hash(manifest_data, page_data, index, roles['tree_data'], note, accepted_roles)
        selected = input_hash.round_selection(view, extracted, note, accepted_roles, parameter_root)
        checked = input_hash.inspect_metadata(view, note, accepted_roles, parameter_root)
    elif kind == 'output-hash':
        view = pages.qualified_output_hash(manifest_data, page_data, index, output, accepted_roles)
        selected = output_hash.round_selection(view, extracted, output, accepted_roles, parameter_root)
        checked = output_hash.inspect_metadata(view, output, accepted_roles, parameter_root)
    elif kind == 'asset-hash':
        view = pages.qualified_asset_hash(manifest_data, page_data, nonidentity_data, accepted_roles)
        selected = asset_hash.round_selection(view, extracted, map_data, accepted_roles, parameter_root)
        checked = asset_hash.inspect_metadata(view, map_data, accepted_roles, parameter_root)
    elif kind == 'recovery-hash':
        view = recovery_pages.qualified_hash(manifest_data, page_data, index, recovery, output, accepted_roles, parameter_root)
        selected = recovery_hash.round_selection(view, extracted, recovery, output, accepted_roles, parameter_root)
        checked = recovery_hash.inspect_metadata(view, recovery, output, accepted_roles, parameter_root)
    else:
        raise relation.RelationError('actual typed permutation task required')
    return selected, checked, dict(metadata={}, readonly_lcs=list(accepted_roles['observed'].values()))


def generate_component(manifest_data, roles64_data, roles73_data, nonidentity_data,
                       accepted_roles, parameter_root, receipt, *, page_data=None,
                       hash_template=None, source_base=None, actual_base=None):
    """Bounded candidate-source recipe; persist/discard each yielded module.

The root diagnostic caller first runs an admitted independent replay_t4 for
each task and freezes every original input/source inventory. For permutations,
hash_template must itself be reaccepted by typed_hash_context from its original
qualified parent/page and independently replayed extraction. source_base names
the exact audited source template; use actual_base for disjoint page modules.
With no template this emits the full native65 template, which must be audited
before reuse. Mismatching parameters/LCs/rows fail rather than falling back to
an assumed permutation equation. All outputs remain candidates until audited.
"""
    from circuits import generate_transfer_note_spend as spend_completion
    from circuits import generate_note_tree_completion as tree_completion
    from circuits import transfer_note_output_bindings as output_bindings
    from circuits import transfer_note_hash_renaming as renaming
    kind, index = receipt.get('component'), receipt.get('index'); _task(kind, index)
    context = prepare_parents(manifest_data, roles64_data, roles73_data, nonidentity_data, accepted_roles)
    wanted = _parent_ids(context)
    _map_data(context, kind)
    if receipt.get('kind') != 'actual-component-row-ingress' or receipt.get('parent_sha256') != wanted:
        raise relation.RelationError('actual generator original parent receipt mismatch')
    if receipt.get('pending_page_sha256') != (None if page_data is None else _sha(page_data)):
        raise relation.RelationError('actual generator original pending page receipt mismatch')
    extracted = receipt['extraction']; roles = context['roles']; note = roles['note_data']; output = roles['output_data']
    recovery = context['recovery_data']; map_data = _map_data(context, kind)
    if kind == 'asset-map':
        yield from maps.generate_row_modules(map_data, extracted, accepted_roles).items()
        yield from maps.generate_comparison_modules(map_data, extracted, accepted_roles).items()
        yield 'RuntimeTransferAssetMapEncoding', maps.generate_encoding_module(map_data, extracted, accepted_roles)
        from circuits import transfer_asset_map_image, transfer_asset_map_choice, transfer_asset_map_curve
        yield transfer_asset_map_image.generate(map_data, extracted, accepted_roles)
        yield transfer_asset_map_choice.generate(map_data, extracted, accepted_roles)
        yield transfer_asset_map_curve.generate(map_data, extracted, accepted_roles)
        from circuits import transfer_asset_map_cofactor, transfer_asset_map_native
        from circuits import transfer_asset_map_native_constructor, transfer_asset_map_completion
        from circuits import transfer_asset_map_total_inverse_completion, transfer_asset_map_parity_completion
        from circuits import transfer_asset_map_comparator_completion
        yield from transfer_asset_map_cofactor.generate_doubles(map_data, extracted, accepted_roles).items()
        yield transfer_asset_map_cofactor.generate(map_data, extracted, accepted_roles)
        yield transfer_asset_map_native.generate(map_data, extracted, accepted_roles)
        yield transfer_asset_map_cofactor.generate_native(map_data, extracted, accepted_roles)
        yield transfer_asset_map_native_constructor.generate(map_data, extracted, accepted_roles)
        yield from transfer_asset_map_completion.generate_materializations(map_data, extracted, accepted_roles).items()
        yield transfer_asset_map_total_inverse_completion.generate(map_data, extracted, accepted_roles)
        yield transfer_asset_map_completion.generate_native_bits(map_data, extracted, accepted_roles)
        yield transfer_asset_map_parity_completion.generate(map_data, extracted, accepted_roles)
        yield from transfer_asset_map_comparator_completion.generate_chunks(map_data, extracted, accepted_roles).items()
        yield transfer_asset_map_comparator_completion.generate(map_data, extracted, accepted_roles)
        from circuits import transfer_asset_map_materialization_sequence, transfer_asset_map_first_cubic_completion
        yield from transfer_asset_map_materialization_sequence.generate_supports(map_data, extracted, accepted_roles).items()
        yield transfer_asset_map_materialization_sequence.generate(map_data, extracted, accepted_roles)
        yield transfer_asset_map_first_cubic_completion.generate(map_data, extracted, accepted_roles)
    elif kind == 'asset-inverse':
        yield generator.generate_sound(nonidentity_data, extracted, accepted_roles)
        yield generator.generate_completion(nonidentity_data, extracted, accepted_roles)
        yield from generator.generate_kept_boundaries(nonidentity_data, extracted, accepted_roles).items()
    elif kind == 'spend':
        yield 'RuntimeTransferNoteSpend', spend.generate(note, extracted, accepted_roles)
        yield 'RuntimeTransferNoteSpendCompletion', spend_completion.generate_completion(note, extracted, accepted_roles)
    elif kind == 'outputs':
        yield 'RuntimeTransferNoteOutputBindings', outputs.generate(output, extracted, accepted_roles)
        yield 'RuntimeTransferOutputReceiverCompletion', outputs.generate_receiver_completion(output, extracted, accepted_roles)
        for slot in (0, 1): yield output_bindings.generate_capsule_copy(output, extracted, accepted_roles, slot)
    elif kind == 'input-range':
        slot, role = divmod(index, 2); role = ('amount', 'position')[role]
        yield f'RuntimeTransferNote{slot}{role.title()}Range', ranges.generate(note, extracted, accepted_roles, slot, role)
    elif kind == 'output-range':
        yield f'RuntimeTransferOutput{index}AmountRange', outputs.generate_range(output, extracted, accepted_roles, index)
    elif kind == 'recovery-range':
        yield f'RuntimeTransferRecovery{index}RandomizerRange', recovery_ranges.generate(recovery, extracted, output, accepted_roles, index)
    elif kind == 'tree':
        yield from tree_completion.generate(roles['tree_data'], extracted, note, accepted_roles)
    elif kind == 'recovery-bindings':
        yield capsules.generate_sound(recovery, extracted, output, accepted_roles)
        for slot in (0, 1):
            for role in capsules.ROLES: yield capsules.generate_completion(recovery, extracted, output, accepted_roles, slot, role)
    elif kind == 'recovery-inverses':
        yield capsules.generate_inverse_sound(recovery, extracted, output, accepted_roles)
        for slot in (0, 1):
            for occurrence in (0, 1): yield capsules.generate_inverse_completion(recovery, extracted, output, accepted_roles, slot, occurrence)
    elif kind == 'output-hash-binding':
        view = pages.qualified_output_hash(manifest_data, page_data, index, output, accepted_roles)
        yield output_bindings.generate(view, extracted, output, accepted_roles)
    else:
        actual = typed_hash_context(manifest_data, roles64_data, roles73_data, nonidentity_data,
                                   accepted_roles, parameter_root, kind, index, page_data, extracted)
        if hash_template is None:
            if source_base is not None: raise relation.RelationError('actual full template has no imported source base')
            if kind == 'asset-hash':
                from circuits import generate_asset_hash_completion
                view = pages.qualified_asset_hash(manifest_data, page_data, nonidentity_data, accepted_roles)
                yield from generate_asset_hash_completion.generate(view, extracted, map_data,
                    accepted_roles, parameter_root, base=actual_base)
            else:
                yield from renaming.generate_template_context(actual, actual_base)
        else:
            yield from renaming.generate_compact_sound_context(hash_template, actual, source_base, actual_base)
