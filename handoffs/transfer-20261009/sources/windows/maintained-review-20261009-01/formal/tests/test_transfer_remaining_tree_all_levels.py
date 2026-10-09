"""Bounded physical-template fixtures, never real captures or kernel evidence."""
import copy, json, unittest
from unittest.mock import patch
from blake3 import blake3
from circuits import transfer_remaining_pages as pages, transfer_remaining_tree_all_levels as all_levels
from circuits.transfer_relation import RelationError
from tests.test_transfer_remaining_tree_bundle import fixture as initial_fixture
from tests.test_transfer_remaining_pages import encoded


def fixture():
    manifest, page, accepted, _ = initial_fixture()
    m, p = json.loads(manifest), json.loads(page)
    tree = [record for record in p['records'] if record['scope'] == 'sender' and record['tag'] == 'tree-level']
    hashes = [item for item in p['calls'] if item['scope'] == 'sender']
    position = tree[0]['values'][13]
    previous = tree[0]['values'][0]
    for i, record in enumerate(tree):
        refs = [{'source': [1, 64000 + 20 * i + j]} for j in range(14)]
        refs[0] = previous
        refs[1:3] = [{'source': [1, 61000 + 2 * i + j]} for j in range(2)]
        refs[13] = position
        record['values'] = refs
        hashes[i + 1]['inputs'][1:] = refs[8:12]
        hashes[i + 1]['output'] = hashes[i + 1]['blocks'][-1]['after'][1] = refs[12]
        previous = refs[12]
    for record in p['records']:
        if record['scope'] == 'sender' and record['tag'] == 'computed-root': record['values'][0] = previous
    handles = sorted({tuple(value['source']) for record in p['records'] if record['scope'] in ('caller', 'sender') for value in record['values'] if 'source' in value})
    p['expressions'] = [dict(source=list(handle), terms=[[handle[1] + 3, f'{1:064x}']]) for handle in handles]
    page = encoded(p); m['pages'][0].update(bytes=len(page), blake3=blake3(page).hexdigest()); manifest = encoded(m)
    _, requirements = all_levels._requirements(manifest, page, accepted)
    physical = []; signatures = {}
    for required, products, squares in requirements:
        for row in required:
            if row not in physical: physical.append(row)
        for _, minus, plus, out, numerator in products:
            key = (minus, plus, out, numerator)
            if key in signatures: continue
            auxiliary = ((72000 + len(physical), 1),)
            if out is None: out = ((73000 + len(physical), 1),)
            physical.extend([(minus, auxiliary), (plus, pages.combine(auxiliary, out, 4))])
            if numerator is not None: physical.append((pages.combine(out, numerator, -1), ()))
            signatures[key] = True
        assert not squares
    rows = [dict(row=i, a=[[c, f'{v:064x}'] for c, v in a], b=[[c, f'{v:064x}'] for c, v in b]) for i, (a, b) in enumerate(physical)]
    identity = dict(relation_digest=m['relation_digest'], domain_size=m['domain_size'], stored_rows=m['full_rows'])
    def inspect(stream, expected_relation, row_observer):
        assert expected_relation == identity['relation_digest']
        for row in rows: row_observer(row)
        return identity
    return manifest, page, accepted, inspect


class AllTreeLevelsTests(unittest.TestCase):
    def accepted(self):
        manifest, page, accepted, inspect = fixture()
        with patch.object(all_levels.arithmetic.relation, 'inspect', side_effect=inspect) as replay:
            extracted = all_levels.extract(manifest, page, object(), accepted)
        self.assertEqual(replay.call_count, 1)
        return manifest, page, accepted, extracted

    def test_one_stream_all_sixteen_original_level_templates(self):
        manifest, page, accepted, extracted = self.accepted()
        self.assertEqual(tuple(extracted['parts']), all_levels.KINDS)
        self.assertEqual(extracted['ordinary_replays'], 1)
        for i in range(16):
            part = extracted['parts'][f'level{i:03}']
            selected = pages.tree_level_certificates(manifest, page, i, part, accepted)
            self.assertEqual(selected['level'], i)
            self.assertEqual(len(selected['certificates']), 6)
        self.assertLess(len(extracted['selected_rows']), sum(len(part['selected_rows']) for part in extracted['parts'].values()))

    def test_changed_level_missing_level_and_extra_row_refused(self):
        manifest, page, accepted, extracted = self.accepted()
        for mode in ('changed', 'missing', 'extra', 'bool', 'identity'):
            bad = copy.deepcopy(extracted)
            if mode == 'changed': bad['parts']['level015']['tree_level'] = 14
            elif mode == 'missing': del bad['parts']['level007']
            elif mode == 'extra':
                row = copy.deepcopy(bad['selected_rows'][-1]); row['row'] += 1; bad['selected_rows'].append(row)
            elif mode == 'bool': bad['ordinary_replays'] = True
            else: bad['parts']['level009']['identity']['stored_rows'] -= 1
            with self.assertRaises(RelationError): all_levels.validate(manifest, page, bad, accepted)


if __name__ == '__main__': unittest.main()
