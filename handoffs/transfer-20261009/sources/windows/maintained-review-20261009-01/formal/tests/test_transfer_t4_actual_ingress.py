"""Small real row-template replays; no runtime qualification or kernel claims."""
import hashlib
import io
import json
import unittest
from unittest.mock import patch
from integration import transfer_t4_actual_ingress as ingress
from circuits import transfer_relation as relation
from tests.test_transfer_asset_generator_nonidentity import inverse_fixture
from tests.test_transfer_t4_pages import manifest
from circuits import transfer_recovery_pages
from circuits.transfer_note_t4_pages import encoded


class ActualT4IngressTests(unittest.TestCase):
    def test_remaining_membership_dispatch_reaccepts_selected_rows(self):
        from circuits import transfer_remaining_pages as remaining
        selected = dict(identity=dict(raw_sha256='e'*64))
        stream = object(); caller = dict(metadata_sha256='c'*64)
        # Dispatch only; mock returns no actual observation or replay credit.
        with patch.object(remaining, 'extract_membership', return_value=selected) as extract, \
             patch.object(remaining, 'membership_certificates') as reaccept:
            receipt = ingress.replay_remaining(b'manifest', b'roles', stream, caller, None,
                                               'remaining-membership', 0)
        extract.assert_called_once_with(b'manifest', b'roles', stream, caller)
        reaccept.assert_called_once_with(b'manifest', b'roles', selected, caller)
        self.assertEqual(receipt['component'], 'remaining-membership')
        with patch.object(remaining, 'extract_membership') as extract:
            with self.assertRaises(relation.RelationError):
                ingress.replay_remaining(b'manifest', b'roles', stream, caller, None,
                                        'remaining-membership', 1)
            extract.assert_not_called()

    def test_remaining_tree_dispatch_reaccepts_fresh_selection(self):
        from circuits import transfer_remaining_pages as remaining
        selected = dict(identity=dict(raw_sha256='e'*64))
        stream = object(); caller = dict(metadata_sha256='c'*64)
        # Dispatch isolation only. The tree parser and physical templates have
        # separate mutation tests; this mock establishes no replay success.
        with patch.object(remaining, 'extract_tree_level', return_value=selected) as extract, \
             patch.object(remaining, 'tree_level_certificates') as reaccept:
            receipt = ingress.replay_remaining(b'manifest', b'roles', stream, caller, None,
                                               'remaining-tree-level', 15)
        extract.assert_called_once_with(b'manifest', b'roles', 15, stream, caller)
        reaccept.assert_called_once_with(b'manifest', b'roles', 15, selected, caller)
        self.assertEqual(receipt['component'], 'remaining-tree-level')
        self.assertEqual(receipt['index'], 15)
        self.assertEqual(receipt['pending_page_sha256'], hashlib.sha256(b'roles').hexdigest())
        with patch.object(remaining, 'extract_tree_level', side_effect=relation.RelationError('wrong level')):
            with self.assertRaises(relation.RelationError):
                ingress.replay_remaining(b'manifest', b'roles', stream, caller, None,
                                        'remaining-tree-level', 16)

    def test_asset_constructor_dispatch_reuses_the_same_strict_receipt_and_page(self):
        from circuits import generate_asset_hash_completion as completion
        context=dict(prefix=dict(parent_metadata_sha256='a'*64),
            roles=dict(original_pending_sha256='b'*64,note_data=b'note',output_data=b'output'),
            recovery_pending_sha256='c'*64,recovery_data=b'recovery',
            map_view=dict(map_data=b'map',parent_metadata_sha256='d'*64))
        extracted=dict(identity=dict(raw_sha256='e'*64))
        page=b'original-pending'
        receipt=ingress._receipt('asset-hash',63,extracted,parents=ingress._parent_ids(context),pending_page=page)
        # Isolate source dispatch only; parent/typed page parsers have their own
        # semantic refusal tests. No mock result is claimed as actual ingress.
        with patch.object(ingress,'prepare_parents',return_value=context), \
             patch.object(ingress,'typed_hash_context',return_value=('selected','checked','roles')), \
             patch.object(ingress.pages,'qualified_asset_hash',return_value=b'qualified-view') as typed, \
             patch.object(completion,'generate',return_value=iter([('Constructor','source')])) as renderer:
            modules=list(ingress.generate_component(b'74',b'64',b'73',b'nonidentity',{},'params',receipt,
                page_data=page,actual_base='RuntimeTransferActualAssetHash'))
            self.assertEqual(modules,[('Constructor','source')])
            typed.assert_called_once_with(b'74',page,b'nonidentity',{})
            renderer.assert_called_once_with(b'qualified-view',extracted,b'map',{},'params',base='RuntimeTransferActualAssetHash')
            changed=dict(receipt,pending_page_sha256='0'*64)
            with self.assertRaises(relation.RelationError):
                list(ingress.generate_component(b'74',b'64',b'73',b'nonidentity',{},'params',changed,
                    page_data=page,actual_base='RuntimeTransferActualAssetHash'))
    def test_nonasset_parent_is_optional_without_invented_identity(self):
        data, caller, _, _, _ = inverse_fixture()
        parent=encoded(manifest(transfer_recovery_pages,json.loads(data)))
        role_view=dict(original_pending_sha256='a'*64,note_data=b'note',tree_data=b'tree',output_data=b'output')
        # Role parsers have separate strict semantic tests; this isolates the
        # optional dependency from their source ownership rather than replacing
        # the original74 manifest checks.
        with patch.object(ingress.pages,'qualified_roles',return_value=role_view), \
             patch.object(ingress.recovery_pages,'qualified_roles',return_value=(b'recovery','b'*64)), \
             patch.object(ingress.generator,'derived_map_view',side_effect=AssertionError('absent asset must not be synthesized')):
            context=ingress.prepare_parents(parent,b'roles64',b'roles73',None,caller)
            identities=ingress._parent_ids(context)
            self.assertEqual(identities['actual74'],hashlib.sha256(parent).hexdigest())
            self.assertNotIn('nonidentity',identities)
            for kind in ('spend','outputs','recovery-hash','recovery-inverses','tree'):
                self.assertIsNone(ingress._map_data(context,kind))
            for kind in ('asset-map','asset-inverse','asset-hash'):
                source=io.BytesIO(b'unread')
                with self.assertRaisesRegex(relation.RelationError,'qualified nonidentity parent'):
                    ingress.replay_t4(parent,b'roles64',b'roles73',None,source,caller,None,kind,
                        63 if kind=='asset-hash' else None)
                self.assertEqual(source.tell(),0)
            corrupted=json.loads(parent);corrupted['pages'][72]['role']='secret'
            with self.assertRaises(relation.RelationError):
                ingress.prepare_parents(encoded(corrupted),b'roles64',b'roles73',None,caller)

    def test_complete_map_and_inverse_each_replay_original_stream_and_parent(self):
        data, caller, stream, _, _ = inverse_fixture()
        raw = stream.read()
        parent = hashlib.sha256(data).hexdigest()
        for component in ('asset-map', 'asset-inverse'):
            source = io.BytesIO(raw)
            receipt = ingress.replay_asset(data, source, caller, component)
            self.assertEqual(source.tell(), len(raw))
            self.assertEqual(receipt['parent_sha256'], {'nonidentity': parent})
            self.assertEqual(receipt['original_row_stream_sha256'], hashlib.sha256(raw).hexdigest())
            self.assertEqual(receipt['extraction']['identity']['relation_digest'], caller['metadata']['relation_digest'])
            self.assertEqual(receipt['extraction']['identity']['source_public'], json.loads(raw.splitlines()[0])['source_public'])
            self.assertEqual(receipt['kind'], 'actual-component-row-ingress')
            self.assertNotIn('qualification', receipt)
            self.assertNotIn('ordinary_full_ordered_rows_equal', receipt)
        self.assertEqual(receipt['parser_view_sha256'], parent)
        self.assertEqual(len(receipt['extraction']['selected_rows']), 4)

    def test_truncation_trailing_and_changed_original_rows_refuse(self):
        data, caller, stream, _, _ = inverse_fixture()
        raw = stream.read(); lines = raw.splitlines(keepends=True)
        altered = json.loads(lines[-2]); altered['a'][0][1] = f'{2:064x}'
        changed = b''.join([*lines[:-2], encoded(altered), lines[-1]])
        for component in ('asset-map', 'asset-inverse'):
            for invalid in (b''.join(lines[:-1]), raw + b'x', changed):
                with self.assertRaises(relation.RelationError):
                    ingress.replay_asset(data, io.BytesIO(invalid), caller, component)

    def test_exact_local_tasks_and_full74_refusal_before_row_access(self):
        selected = ingress.tasks()
        self.assertEqual(len(selected), 136)
        self.assertEqual(len(set(selected)), 136)
        self.assertEqual([index for kind, index in selected if kind == 'tree'], list(range(48)))
        self.assertEqual([index for kind, index in selected if kind == 'recovery-hash'], list(range(65, 73)))
        self.assertEqual([index for kind, index in selected if kind == 'output-hash-binding'], [56, 58, 60, 62])
        data, caller, _, _, _ = inverse_fixture()
        parent = manifest(transfer_recovery_pages, json.loads(data))
        parent['pages'][72]['role'] = 'secret'
        for kind, index in (('input-hash', 0), ('asset-map', None), ('recovery-inverses', None)):
            source = io.BytesIO(b'unread')
            with self.assertRaises(relation.RelationError):
                ingress.replay_t4(encoded(parent), b'{}', b'{}', data, source, caller, None, kind, index)
            self.assertEqual(source.tell(), 0)
        for kind, index in (('tree', True), ('tree', 48), ('recovery-hash', 64), ('output-hash-binding', 55)):
            with self.assertRaises(relation.RelationError): ingress._task(kind, index)


if __name__ == '__main__':
    unittest.main()
